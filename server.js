require('dotenv').config();
const express = require('express');
const mongoose = require('mongoose');
const cookieParser = require('cookie-parser');
const bcrypt = require('bcryptjs');
const jwt = require('jsonwebtoken');
const crypto = require('crypto');
const path = require('path');
const fs = require('fs');
const http = require('http');
const WebSocket = require('ws');
const cors = require('cors');
const compression = require('compression');
const helmet = require('helmet');
const rateLimit = require('express-rate-limit');

const app = express();
const server = http.createServer(app);

// ═══════════════════════════════════════════════════════════════
// CONFIGURATION
// ═══════════════════════════════════════════════════════════════

const IS_RENDER = !!process.env.RENDER;
const RENDER_URL = process.env.RENDER_EXTERNAL_URL;
const RENDER_HOSTNAME = process.env.RENDER_EXTERNAL_HOSTNAME;
const WEBSITE_URL = process.env.WEBSITE_URL || 'https://tublox.vercel.app';

console.log('╔══════════════════════════════════════════════════════════╗');
console.log('║       TuBlox Game Server v1.0 — Render Edition          ║');
console.log('╚══════════════════════════════════════════════════════════╝');
console.log(`[Boot] Platform: ${IS_RENDER ? 'Render' : 'Local'}`);
console.log(`[Boot] Website: ${WEBSITE_URL}`);
if (RENDER_URL) console.log(`[Boot] URL: ${RENDER_URL}`);

// ═══════════════════════════════════════════════════════════════
// SERVER ANTICHEAT
// ═══════════════════════════════════════════════════════════════

class ServerAntiCheat {
    constructor() {
        this.config = {
            maxWalkSpeed: 8.0,
            maxSprintSpeed: 14.0,
            maxSwimSpeed: 6.0,
            maxFallSpeed: 60.0,
            maxJumpVelocity: 12.0,
            maxAirTime: 3.0,
            maxHoverTime: 1.5,
            minFallSpeed: 0.5,
            maxTeleportDistance: 20.0,
            maxPacketsPerSecond: 60,
            maxStateUpdatesPerSecond: 35,
            maxChatMessagesPerMinute: 30,
            maxConnectionsPerIP: 5,
            warnThreshold: 15,
            kickThreshold: 40,
            banThreshold: 80,
            scoreDecayPerSecond: 0.3,
            minUpdateInterval: 15,
            maxUpdateInterval: 5000,
            gracePeriod: 5000,
            gravity: 20.0
        };
        
        this.players = new Map();
        this.ipConnections = new Map();
        this.bannedIPs = new Set();
        this.bannedOdilIds = new Set();
        this.chatCounts = new Map();
        this.onKick = null;
        this.onBan = null;
        this.onWarn = null;
        this.onCorrectPosition = null;
        this.adminIds = new Set([1]);
        this.startDecayTimer();
        console.log('[AntiCheat] Server AntiCheat v1.0 initialized');
    }

    log(msg) {
        console.log(`[AC] ${msg}`);
    }

    registerPlayer(odilId, username, ip, spawnPosition) {
        if (this.bannedOdilIds.has(odilId)) {
            this.log(`BLOCKED: Banned player #${odilId}`);
            return { allowed: false, reason: 'You are banned from this server' };
        }
        
        if (this.bannedIPs.has(ip)) {
            this.log(`BLOCKED: Banned IP ${ip}`);
            return { allowed: false, reason: 'Your IP is banned' };
        }
        
        if (!this.ipConnections.has(ip)) {
            this.ipConnections.set(ip, new Set());
        }
        const ipConns = this.ipConnections.get(ip);
        
        if (ipConns.size >= this.config.maxConnectionsPerIP && !this.adminIds.has(odilId)) {
            this.log(`BLOCKED: Too many connections from ${ip}`);
            return { allowed: false, reason: 'Too many connections from your IP' };
        }
        
        ipConns.add(odilId);
        
        const now = Date.now();
        const isAdmin = this.adminIds.has(odilId);
        
        this.players.set(odilId, {
            odilId,
            username,
            ip,
            position: { ...spawnPosition },
            lastValidPosition: { ...spawnPosition },
            velocity: { x: 0, y: 0, z: 0 },
            isGrounded: true,
            isJumping: false,
            isSprinting: false,
            isInWater: false,
            lastUpdateTime: now,
            connectedAt: now,
            lastGroundedTime: now,
            graceUntil: now + this.config.gracePeriod,
            airTime: 0,
            hoverTime: 0,
            violationScore: 0,
            violations: { speed: 0, fly: 0, teleport: 0, packet: 0, invalid: 0 },
            packetsThisSecond: 0,
            packetResetTime: now,
            statesThisSecond: 0,
            stateResetTime: now,
            isFrozen: false,
            isAdmin
        });
        
        this.log(`Registered: ${username} (#${odilId}) from ${ip}${isAdmin ? ' [ADMIN]' : ''}`);
        return { allowed: true };
    }

    unregisterPlayer(odilId) {
        const player = this.players.get(odilId);
        if (player) {
            const ipConns = this.ipConnections.get(player.ip);
            if (ipConns) {
                ipConns.delete(odilId);
                if (ipConns.size === 0) this.ipConnections.delete(player.ip);
            }
            this.log(`Unregistered: ${player.username} (#${odilId}) | Score: ${player.violationScore.toFixed(1)} | Violations: ${JSON.stringify(player.violations)}`);
            this.players.delete(odilId);
        }
    }

    checkPacketRate(odilId, isStatePacket = false) {
        const player = this.players.get(odilId);
        if (!player || player.isAdmin) return { allowed: true };
        
        const now = Date.now();
        
        if (now - player.packetResetTime > 1000) {
            player.packetsThisSecond = 0;
            player.packetResetTime = now;
        }
        if (now - player.stateResetTime > 1000) {
            player.statesThisSecond = 0;
            player.stateResetTime = now;
        }
        
        player.packetsThisSecond++;
        if (isStatePacket) player.statesThisSecond++;
        
        if (player.packetsThisSecond > this.config.maxPacketsPerSecond) {
            this.addViolation(odilId, 'packet', 5, 'Packet spam');
            return { allowed: false, reason: 'Rate limited' };
        }
        
        if (isStatePacket && player.statesThisSecond > this.config.maxStateUpdatesPerSecond) {
            return { allowed: false, reason: 'State rate limited' };
        }
        
        return { allowed: true };
    }

    checkChatRate(odilId) {
        const player = this.players.get(odilId);
        if (!player) return { allowed: false };
        if (player.isAdmin) return { allowed: true };
        
        const now = Date.now();
        if (!this.chatCounts.has(odilId)) {
            this.chatCounts.set(odilId, { count: 0, resetTime: now });
        }
        
        const chat = this.chatCounts.get(odilId);
        if (now - chat.resetTime > 60000) {
            chat.count = 0;
            chat.resetTime = now;
        }
        
        chat.count++;
        if (chat.count > this.config.maxChatMessagesPerMinute) {
            this.addViolation(odilId, 'packet', 3, 'Chat spam');
            return { allowed: false, reason: 'Chat rate limited' };
        }
        
        return { allowed: true };
    }

    validatePlayerState(odilId, data) {
        const player = this.players.get(odilId);
        if (!player) return { valid: false, action: 'kick', reason: 'Unknown player' };
        
        if (player.isAdmin) {
            this.updatePlayerState(player, data);
            return { valid: true };
        }
        
        const now = Date.now();
        const deltaTime = Math.min((now - player.lastUpdateTime) / 1000, 1.0);
        
        if (now < player.graceUntil) {
            this.updatePlayerState(player, data);
            return { valid: true };
        }
        
        if (player.isFrozen) {
            return { 
                valid: false, 
                action: 'rollback', 
                reason: 'You are frozen',
                correctedPosition: player.lastValidPosition 
            };
        }
        
        const dataCheck = this.validateData(data);
        if (!dataCheck.valid) {
            this.addViolation(odilId, 'invalid', 15, dataCheck.reason);
            return { valid: false, action: 'rollback', reason: dataCheck.reason, correctedPosition: player.lastValidPosition };
        }
        
        const newPos = { x: data.posX, y: data.posY, z: data.posZ };
        const newVel = { x: data.velX || 0, y: data.velY || 0, z: data.velZ || 0 };
        
        const teleport = this.checkTeleport(player, newPos, deltaTime);
        if (!teleport.valid) {
            this.addViolation(odilId, 'teleport', teleport.severity, teleport.reason);
            if (teleport.severity >= 10) {
                return { valid: false, action: 'rollback', reason: teleport.reason, correctedPosition: player.lastValidPosition };
            }
        }
        
        const speed = this.checkSpeed(player, newPos, deltaTime, data);
        if (!speed.valid) {
            this.addViolation(odilId, 'speed', speed.severity, speed.reason);
            if (speed.severity >= 8) {
                return { valid: false, action: 'rollback', reason: speed.reason, correctedPosition: player.lastValidPosition };
            }
        }
        
        const fly = this.checkFly(player, newPos, newVel, deltaTime, data);
        if (!fly.valid) {
            this.addViolation(odilId, 'fly', fly.severity, fly.reason);
            if (fly.severity >= 10) {
                return { valid: false, action: 'rollback', reason: fly.reason, correctedPosition: player.lastValidPosition };
            }
        }
        
        this.updatePlayerState(player, data);
        
        const action = this.checkThresholds(odilId);
        if (action) return { valid: false, action: action.type, reason: action.reason };
        
        return { valid: true };
    }

    validateData(data) {
        const fields = ['posX', 'posY', 'posZ', 'velX', 'velY', 'velZ'];
        for (const f of fields) {
            if (data[f] !== undefined && (typeof data[f] !== 'number' || !isFinite(data[f]))) {
                return { valid: false, reason: `Invalid ${f}` };
            }
        }
        
        if (Math.abs(data.posX) > 50000 || Math.abs(data.posY) > 50000 || Math.abs(data.posZ) > 50000) {
            return { valid: false, reason: 'Position out of bounds' };
        }
        
        if (data.posY < -500) {
            return { valid: false, reason: 'Below world' };
        }
        
        return { valid: true };
    }

    checkTeleport(player, newPos, dt) {
        const dx = newPos.x - player.position.x;
        const dy = newPos.y - player.position.y;
        const dz = newPos.z - player.position.z;
        const dist = Math.sqrt(dx*dx + dy*dy + dz*dz);
        
        if (dist > this.config.maxTeleportDistance) {
            return { valid: false, severity: 20, reason: `Teleport: ${dist.toFixed(1)} blocks` };
        }
        
        const maxDist = (player.isSprinting ? this.config.maxSprintSpeed : this.config.maxWalkSpeed) * dt * 2.5 + 3;
        if (dist > maxDist && dt < 0.5) {
            return { valid: false, severity: 8, reason: `Speed anomaly: ${(dist/dt).toFixed(1)} b/s` };
        }
        
        return { valid: true };
    }

    checkSpeed(player, newPos, dt, data) {
        if (dt <= 0.01) return { valid: true };
        
        const dx = newPos.x - player.position.x;
        const dz = newPos.z - player.position.z;
        const hDist = Math.sqrt(dx*dx + dz*dz);
        const hSpeed = hDist / dt;
        
        let maxSpeed = this.config.maxWalkSpeed;
        if (data.isSprinting) maxSpeed = this.config.maxSprintSpeed;
        if (data.isInWater) maxSpeed = this.config.maxSwimSpeed;
        maxSpeed *= 1.4;
        
        if (hSpeed > maxSpeed * 2.5) {
            return { valid: false, severity: 15, reason: `Speed hack: ${hSpeed.toFixed(1)} b/s` };
        }
        
        if (hSpeed > maxSpeed) {
            return { valid: false, severity: 4, reason: `Speed: ${hSpeed.toFixed(1)} b/s` };
        }
        
        return { valid: true };
    }

    checkFly(player, newPos, newVel, dt, data) {
        if (data.isInWater) {
            player.airTime = 0;
            player.hoverTime = 0;
            return { valid: true };
        }
        
        if (data.isGrounded) {
            player.airTime = 0;
            player.hoverTime = 0;
            player.lastGroundedTime = Date.now();
            return { valid: true };
        }
        
        player.airTime += dt;
        
        if (Math.abs(newVel.y) < 0.3 && player.airTime > 0.5) {
            player.hoverTime += dt;
        } else {
            player.hoverTime = Math.max(0, player.hoverTime - dt * 2);
        }
        
        if (newVel.y > this.config.maxJumpVelocity * 1.2 && !data.isJumping && player.airTime > 0.3) {
            return { valid: false, severity: 12, reason: `Fly up: velY=${newVel.y.toFixed(1)}` };
        }
        
        if (player.airTime > 1.2 && newVel.y > -this.config.minFallSpeed && !data.isJumping) {
            return { valid: false, severity: 10, reason: `Not falling: velY=${newVel.y.toFixed(1)}` };
        }
        
        if (player.hoverTime > this.config.maxHoverTime) {
            return { valid: false, severity: 15, reason: `Hover: ${player.hoverTime.toFixed(1)}s` };
        }
        
        if (player.airTime > this.config.maxAirTime) {
            return { valid: false, severity: 20, reason: `Fly: ${player.airTime.toFixed(1)}s in air` };
        }
        
        return { valid: true };
    }

    addViolation(odilId, type, severity, reason) {
        const player = this.players.get(odilId);
        if (!player) return;
        
        player.violationScore += severity;
        player.violations[type] = (player.violations[type] || 0) + 1;
        
        this.log(`VIOLATION: ${player.username} (#${odilId}) - ${type}: ${reason} [+${severity}] (Total: ${player.violationScore.toFixed(1)})`);
        
        if (this.onWarn && severity >= 5) {
            this.onWarn(odilId, `[AntiCheat] ${reason}`);
        }
    }

    checkThresholds(odilId) {
        const player = this.players.get(odilId);
        if (!player) return null;
        
        if (player.violationScore >= this.config.banThreshold) {
            this.banPlayer(odilId, 'Too many violations - auto ban');
            return { type: 'ban', reason: 'Banned by AntiCheat' };
        }
        
        if (player.violationScore >= this.config.kickThreshold) {
            this.kickPlayer(odilId, 'Too many violations');
            return { type: 'kick', reason: 'Kicked by AntiCheat' };
        }
        
        return null;
    }

    kickPlayer(odilId, reason) {
        const player = this.players.get(odilId);
        if (!player) return;
        this.log(`KICK: ${player.username} (#${odilId}) - ${reason}`);
        if (this.onKick) this.onKick(odilId, reason);
    }

    banPlayer(odilId, reason) {
        const player = this.players.get(odilId);
        if (!player) return;
        this.log(`BAN: ${player.username} (#${odilId}) IP:${player.ip} - ${reason}`);
        this.bannedOdilIds.add(odilId);
        this.bannedIPs.add(player.ip);
        if (this.onBan) this.onBan(odilId, reason, player.ip);
    }

    freezePlayer(odilId, freeze) {
        const player = this.players.get(odilId);
        if (player) {
            player.isFrozen = freeze;
            this.log(`${freeze ? 'FREEZE' : 'UNFREEZE'}: ${player.username} (#${odilId})`);
        }
    }

    setAdmin(odilId, isAdmin) {
        if (isAdmin) {
            this.adminIds.add(odilId);
        } else {
            this.adminIds.delete(odilId);
        }
        const player = this.players.get(odilId);
        if (player) player.isAdmin = isAdmin;
    }

    resetPlayer(odilId) {
        const player = this.players.get(odilId);
        if (player) {
            player.violationScore = 0;
            player.violations = { speed: 0, fly: 0, teleport: 0, packet: 0, invalid: 0 };
            player.airTime = 0;
            player.hoverTime = 0;
            player.graceUntil = Date.now() + this.config.gracePeriod;
            this.log(`RESET: ${player.username} (#${odilId})`);
        }
    }

    grantGrace(odilId, duration = null) {
        const player = this.players.get(odilId);
        if (player) {
            player.graceUntil = Date.now() + (duration || this.config.gracePeriod);
            player.airTime = 0;
            player.hoverTime = 0;
        }
    }

    updatePlayerState(player, data) {
        player.lastValidPosition = { ...player.position };
        player.position = { x: data.posX, y: data.posY, z: data.posZ };
        player.velocity = { x: data.velX || 0, y: data.velY || 0, z: data.velZ || 0 };
        player.isGrounded = !!data.isGrounded;
        player.isJumping = !!data.isJumping;
        player.isSprinting = !!data.isSprinting;
        player.isInWater = !!data.isInWater;
        player.lastUpdateTime = Date.now();
    }

    startDecayTimer() {
        setInterval(() => {
            this.players.forEach(player => {
                if (player.violationScore > 0) {
                    player.violationScore = Math.max(0, player.violationScore - this.config.scoreDecayPerSecond);
                }
            });
        }, 1000);
    }

    getStats(odilId) {
        const player = this.players.get(odilId);
        if (!player) return null;
        return {
            odilId: player.odilId,
            username: player.username,
            score: player.violationScore,
            violations: { ...player.violations },
            isFrozen: player.isFrozen,
            isAdmin: player.isAdmin
        };
    }

    getServerStats() {
        return {
            players: this.players.size,
            bannedIPs: this.bannedIPs.size,
            bannedOdilIds: this.bannedOdilIds.size
        };
    }

    unbanIP(ip) {
        this.bannedIPs.delete(ip);
        this.log(`UNBAN IP: ${ip}`);
    }

    unbanPlayer(odilId) {
        this.bannedOdilIds.delete(odilId);
        this.log(`UNBAN: #${odilId}`);
    }
}

const antiCheat = new ServerAntiCheat();

// ═══════════════════════════════════════════════════════════════
// KEEP ALIVE
// ═══════════════════════════════════════════════════════════════

const SELF_URL = RENDER_URL || process.env.SELF_URL;

if (SELF_URL) {
    setInterval(() => {
        const https = require('https');
        const httpModule = require('http');
        const client = SELF_URL.startsWith('https') ? https : httpModule;
        
        client.get(SELF_URL + '/api/health', (res) => {
            console.log('[KeepAlive] Ping OK, status:', res.statusCode);
        }).on('error', (err) => {
            console.log('[KeepAlive] Ping failed:', err.message);
        });
    }, 14 * 60 * 1000);
    
    console.log(`[KeepAlive] Active — pinging ${SELF_URL} every 14min`);
}

// ═══════════════════════════════════════════════════════════════
// EXPRESS MIDDLEWARE
// ═══════════════════════════════════════════════════════════════

app.use(helmet({
    contentSecurityPolicy: false,
    crossOriginEmbedderPolicy: false
}));

app.use(compression());

app.use(cors({
    origin: [
        'https://tublox.vercel.app',
        'https://tublox-servers.onrender.com',
        'http://localhost:3000',
        'http://localhost:5500',
        /\.vercel\.app$/,
        /\.onrender\.com$/
    ],
    credentials: true,
    methods: ['GET', 'POST', 'PUT', 'DELETE', 'PATCH', 'OPTIONS'],
    allowedHeaders: ['Content-Type', 'Authorization', 'Cookie']
}));

const apiLimiter = rateLimit({
    windowMs: 15 * 60 * 1000,
    max: 300,
    standardHeaders: true,
    legacyHeaders: false,
    message: { success: false, message: 'Too many requests, slow down!' }
});

app.use('/api/', apiLimiter);

app.use(express.json({ limit: '10mb' }));
app.use(express.urlencoded({ extended: true }));
app.use(cookieParser());
app.use(express.static(path.join(__dirname, 'public'), {
    maxAge: '1h',
    etag: true
}));

// ═══════════════════════════════════════════════════════════════
// HEALTH CHECK
// ═══════════════════════════════════════════════════════════════

app.get('/api/health', (req, res) => {
    res.json({
        status: 'ok',
        platform: 'render-game-server',
        uptime: process.uptime(),
        games: gameServers.size,
        connections: connectedClients.size,
        wsClients: wss ? wss.clients.size : 0,
        antiCheat: antiCheat.getServerStats(),
        memory: {
            used: Math.round(process.memoryUsage().heapUsed / 1024 / 1024) + 'MB',
            total: Math.round(process.memoryUsage().heapTotal / 1024 / 1024) + 'MB'
        },
        render: IS_RENDER,
        timestamp: Date.now()
    });
});

// ═══════════════════════════════════════════════════════════════
// WEBSOCKET SERVER
// ═══════════════════════════════════════════════════════════════

const wss = new WebSocket.Server({
    server,
    path: '/ws',
    maxPayload: 16 * 1024,
    perMessageDeflate: false
});

const gameServers = new Map();
const connectedClients = new Map();
const onlineSessions = new Map();
const SESSION_TIMEOUT = 2 * 60 * 1000;

const PacketType = {
    CONNECT_REQUEST: 1,
    CONNECT_RESPONSE: 2,
    DISCONNECT: 3,
    PING: 4,
    PONG: 5,
    PLAYER_JOIN: 10,
    PLAYER_LEAVE: 11,
    PLAYER_STATE: 12,
    PLAYER_INPUT: 13,
    PLAYER_LIST: 14,
    WORLD_STATE: 20,
    OBJECT_SPAWN: 21,
    OBJECT_DESTROY: 22,
    OBJECT_UPDATE: 23,
    CHAT_MESSAGE: 30,
    HOST_ASSIGN: 50,
    BUILD_DATA: 51,
    SERVER_INFO: 52,
    AC_WARN: 60,
    AC_KICK: 61,
    AC_CORRECT: 62
};

console.log('[WS] WebSocket server initialized on path /ws');

function sendToClient(ws, data) {
    if (!ws || ws.readyState !== WebSocket.OPEN) return false;
    try {
        ws.send(typeof data === 'string' ? data : JSON.stringify(data));
        return true;
    } catch (err) {
        console.error('[WS] Send error:', err.message);
        return false;
    }
}

function broadcastToGame(gameId, data, excludeOdilId = null) {
    const game = gameServers.get(gameId);
    if (!game) return 0;
    
    const message = typeof data === 'string' ? data : JSON.stringify(data);
    let sentCount = 0;
    
    game.players.forEach((player, odilId) => {
        if (excludeOdilId !== null && odilId === excludeOdilId) return;
        if (player.ws && player.ws.readyState === WebSocket.OPEN) {
            try {
                player.ws.send(message);
                sentCount++;
            } catch (err) {
                console.error(`[WS] Broadcast error to ${player.username}:`, err.message);
            }
        }
    });
    
    return sentCount;
}

function getOrCreateGameServer(gameId) {
    if (!gameServers.has(gameId)) {
        console.log(`[WS] Creating new game server: ${gameId}`);
        gameServers.set(gameId, {
            hostOdilId: null,
            players: new Map(),
            createdAt: Date.now(),
            buildData: null
        });
    }
    return gameServers.get(gameId);
}

function removePlayerFromGame(gameId, odilId) {
    const game = gameServers.get(gameId);
    if (!game) return;
    
    const player = game.players.get(odilId);
    if (!player) return;
    
    console.log(`[WS] Removing player ${player.username} (#${odilId}) from ${gameId}`);
    
    antiCheat.unregisterPlayer(odilId);
    
    game.players.delete(odilId);
    connectedClients.delete(odilId);
    
    User.findOneAndUpdate(
        { odilId: odilId },
        { lastSeen: new Date() }
    ).catch(err => console.error('[DB] Update lastSeen error:', err));
    
    broadcastToGame(gameId, { type: PacketType.PLAYER_LEAVE, odilId });
    
    if (game.hostOdilId === odilId) {
        if (game.players.size > 0) {
            const newHostId = game.players.keys().next().value;
            game.hostOdilId = newHostId;
            const newHost = game.players.get(newHostId);
            if (newHost && newHost.ws) {
                sendToClient(newHost.ws, { type: PacketType.HOST_ASSIGN, isHost: true });
                console.log(`[WS] New host for ${gameId}: ${newHost.username}`);
            }
        } else {
            gameServers.delete(gameId);
            console.log(`[WS] Game server ${gameId} closed (empty)`);
        }
    }
    
    Game.findOneAndUpdate({ id: gameId }, { activePlayers: game ? game.players.size : 0 }).catch(err => console.error('[DB] Update error:', err));
}

// ═══════════════════════════════════════════════════════════════
// ANTICHEAT CALLBACKS
// ═══════════════════════════════════════════════════════════════

antiCheat.onWarn = (odilId, reason) => {
    const client = connectedClients.get(odilId);
    if (client && client.ws) {
        sendToClient(client.ws, {
            type: PacketType.AC_WARN,
            message: reason
        });
        sendToClient(client.ws, {
            type: PacketType.CHAT_MESSAGE,
            odilId: 0,
            username: '[AntiCheat]',
            message: reason
        });
    }
};

antiCheat.onKick = (odilId, reason) => {
    const client = connectedClients.get(odilId);
    if (client && client.ws) {
        sendToClient(client.ws, {
            type: PacketType.AC_KICK,
            reason: `AntiCheat: ${reason}`
        });
        setTimeout(() => {
            if (client.ws && client.ws.readyState === WebSocket.OPEN) {
                client.ws.close(1000, `AntiCheat: ${reason}`);
            }
        }, 100);
    }
    if (client && client.gameId) {
        removePlayerFromGame(client.gameId, odilId);
    }
};

antiCheat.onBan = (odilId, reason, ip) => {
    const client = connectedClients.get(odilId);
    if (client && client.ws) {
        sendToClient(client.ws, {
            type: PacketType.AC_KICK,
            reason: `AntiCheat BAN: ${reason}`
        });
        setTimeout(() => {
            if (client.ws && client.ws.readyState === WebSocket.OPEN) {
                client.ws.close(1000, `AntiCheat BAN: ${reason}`);
            }
        }, 100);
    }
    if (client && client.gameId) {
        removePlayerFromGame(client.gameId, odilId);
    }
    
    // Save ban to database
    Ban.create({
        odilId,
        ip,
        reason,
        bannedAt: new Date()
    }).catch(err => console.error('[DB] Ban save error:', err));
};

antiCheat.onCorrectPosition = (odilId, position) => {
    const client = connectedClients.get(odilId);
    if (client && client.ws) {
        sendToClient(client.ws, {
            type: PacketType.AC_CORRECT,
            posX: position.x,
            posY: position.y,
            posZ: position.z
        });
    }
};

// ═══════════════════════════════════════════════════════════════
// PRESENCE HELPERS
// ═══════════════════════════════════════════════════════════════

function getUserPresence(odilId) {
    const odilIdNum = typeof odilId === 'string' ? parseInt(odilId, 10) : odilId;
    
    if (isNaN(odilIdNum)) {
        return { isOnline: false, currentGame: null };
    }
    
    for (const [gameId, gameServer] of gameServers.entries()) {
        const playerData = gameServer.players.get(odilIdNum);
        
        if (playerData && playerData.ws && playerData.ws.readyState === WebSocket.OPEN) {
            return {
                isOnline: true,
                currentGame: {
                    gameId: gameId,
                    serverId: gameId,
                    joinedAt: playerData.connectedAt 
                        ? new Date(playerData.connectedAt).toISOString() 
                        : new Date().toISOString()
                }
            };
        }
    }
    
    const client = connectedClients.get(odilIdNum);
    if (client && client.ws && client.ws.readyState === WebSocket.OPEN) {
        if (client.gameId) {
            return {
                isOnline: true,
                currentGame: {
                    gameId: client.gameId,
                    serverId: client.gameId,
                    joinedAt: new Date().toISOString()
                }
            };
        }
        return { isOnline: true, currentGame: null };
    }
    
    const session = onlineSessions.get(odilIdNum);
    if (session && (Date.now() - session.lastActivity) < SESSION_TIMEOUT) {
        return { isOnline: true, currentGame: null };
    }
    
    return { isOnline: false, currentGame: null };
}

async function enrichPresenceWithGameInfo(presence) {
    if (!presence.currentGame || !presence.currentGame.gameId) {
        return presence;
    }
    
    try {
        const game = await Game.findOne({ id: presence.currentGame.gameId })
            .select('title thumbnail id')
            .lean();
        
        if (game) {
            presence.currentGame.id = game.id;
            presence.currentGame.title = game.title || game.id;
            presence.currentGame.thumbnail = game.thumbnail || '';
        } else {
            presence.currentGame.id = presence.currentGame.gameId;
            presence.currentGame.title = presence.currentGame.gameId;
            presence.currentGame.thumbnail = '';
        }
    } catch (err) {
        console.error('[Presence] Error:', err.message);
        presence.currentGame.title = presence.currentGame.gameId;
        presence.currentGame.thumbnail = '';
    }
    
    return presence;
}

// ═══════════════════════════════════════════════════════════════
// WEBSOCKET CONNECTION HANDLER
// ═══════════════════════════════════════════════════════════════

wss.on('connection', (ws, req) => {
    const clientIP = req.headers['x-forwarded-for']?.split(',')[0]?.trim() || req.socket.remoteAddress;
    console.log(`[WS] New connection from ${clientIP}`);
    
    let clientOdilId = null;
    let clientGameId = null;
    let clientUsername = null;
    let isConnected = false;

    ws.isAlive = true;
    ws.on('pong', () => { ws.isAlive = true; });

    ws.on('message', async (message) => {
        try {
            const raw = message.toString();
            
            if (raw.length > 10000) {
                console.log(`[WS] Message too large from ${clientIP}: ${raw.length} bytes`);
                ws.close(1009, 'Message too large');
                return;
            }
            
            const data = JSON.parse(raw);
            
            if (data.type !== PacketType.CONNECT_REQUEST && clientOdilId) {
                const rateCheck = antiCheat.checkPacketRate(clientOdilId, data.type === PacketType.PLAYER_STATE);
                if (!rateCheck.allowed) {
                    return;
                }
            }
            
            switch (data.type) {
                case PacketType.CONNECT_REQUEST: {
                    console.log(`[WS] CONNECT_REQUEST from ${clientIP}:`, JSON.stringify(data));
                    
                    if (data.odilId === undefined || data.odilId === null) {
                        sendToClient(ws, { type: PacketType.CONNECT_RESPONSE, success: false, message: 'Invalid odilId' });
                        return;
                    }
                    
                    const parsedOdilId = typeof data.odilId === 'string' ? parseInt(data.odilId, 10) : Number(data.odilId);
                    
                    if (isNaN(parsedOdilId) || parsedOdilId <= 0) {
                        sendToClient(ws, { type: PacketType.CONNECT_RESPONSE, success: false, message: 'Invalid odilId' });
                        return;
                    }

                    clientOdilId = parsedOdilId;
                    clientGameId = data.gameId || 'baseplate';
                    clientUsername = (data.username || `Player${clientOdilId}`).substring(0, 32);
                    
                    const spawnPosition = { x: 0, y: 5, z: 0 };
                    
                    const acResult = antiCheat.registerPlayer(clientOdilId, clientUsername, clientIP, spawnPosition);
                    if (!acResult.allowed) {
                        sendToClient(ws, { 
                            type: PacketType.CONNECT_RESPONSE, 
                            success: false, 
                            message: acResult.reason 
                        });
                        ws.close(1000, acResult.reason);
                        return;
                    }

                    const existingClient = connectedClients.get(clientOdilId);
                    if (existingClient && existingClient.ws !== ws) {
                        console.log(`[WS] Closing existing connection for #${clientOdilId}`);
                        if (existingClient.gameId) {
                            removePlayerFromGame(existingClient.gameId, clientOdilId);
                        }
                        if (existingClient.ws && existingClient.ws.readyState === WebSocket.OPEN) {
                            existingClient.ws.close(1000, 'Reconnecting');
                        }
                    }

                    const game = getOrCreateGameServer(clientGameId);
                    
                    let isHost = false;
                    if (game.hostOdilId === null || game.players.size === 0) {
                        game.hostOdilId = clientOdilId;
                        isHost = true;
                        try {
                            const gameDoc = await Game.findOne({ id: clientGameId });
                            if (gameDoc && gameDoc.buildData) {
                                game.buildData = gameDoc.buildData;
                            }
                        } catch (err) {
                            console.error('[DB] Load buildData error:', err);
                        }
                    }

                    const existingPlayers = [];
                    game.players.forEach((player, odilId) => {
                        if (odilId !== clientOdilId) {
                            existingPlayers.push({
                                odilId,
                                username: player.username,
                                position: { ...player.position }
                            });
                        }
                    });

                    game.players.set(clientOdilId, {
                        ws,
                        username: clientUsername,
                        position: { ...spawnPosition },
                        rotation: { x: 0, y: 0, z: 0 },
                        velocity: { x: 0, y: 0, z: 0 },
                        animationId: 0,
                        isGrounded: false,
                        isJumping: false,
                        isSprinting: false,
                        isInWater: false,
                        lastUpdate: Date.now(),
                        connectedAt: Date.now()
                    });

                    connectedClients.set(clientOdilId, {
                        ws,
                        gameId: clientGameId,
                        username: clientUsername
                    });
                    
                    isConnected = true;

                    console.log(`[WS] ✓ ${clientUsername} (#${clientOdilId}) joined ${clientGameId}`);

                    Game.findOneAndUpdate(
                        { id: clientGameId },
                        { activePlayers: game.players.size }
                    ).catch(err => console.error('[DB] Update error:', err));

                    sendToClient(ws, {
                        type: PacketType.CONNECT_RESPONSE,
                        success: true,
                        odilId: clientOdilId,
                        isHost,
                        spawnX: spawnPosition.x,
                        spawnY: spawnPosition.y,
                        spawnZ: spawnPosition.z,
                        message: 'Connected!'
                    });

                    if (isHost && game.buildData) {
                        sendToClient(ws, { type: PacketType.BUILD_DATA, buildData: game.buildData });
                    }

                    setTimeout(() => {
                        if (ws.readyState !== WebSocket.OPEN) return;
                        
                        for (const player of existingPlayers) {
                            sendToClient(ws, {
                                type: PacketType.PLAYER_JOIN,
                                odilId: player.odilId,
                                username: player.username,
                                posX: player.position.x,
                                posY: player.position.y,
                                posZ: player.position.z
                            });
                        }
                        
                        setTimeout(() => {
                            broadcastToGame(clientGameId, {
                                type: PacketType.PLAYER_JOIN,
                                odilId: clientOdilId,
                                username: clientUsername,
                                posX: spawnPosition.x,
                                posY: spawnPosition.y,
                                posZ: spawnPosition.z
                            }, clientOdilId);
                        }, 100);
                    }, 200);
                    
                    break;
                }

                case PacketType.PLAYER_STATE: {
                    if (!clientGameId || !clientOdilId || !isConnected) break;
                    
                    const game = gameServers.get(clientGameId);
                    if (!game) break;
                    
                    const player = game.players.get(clientOdilId);
                    if (!player) break;

                    const validation = antiCheat.validatePlayerState(clientOdilId, data);
                    
                    if (!validation.valid) {
                        if (validation.action === 'rollback' && validation.correctedPosition) {
                            sendToClient(ws, {
                                type: PacketType.AC_CORRECT,
                                posX: validation.correctedPosition.x,
                                posY: validation.correctedPosition.y,
                                posZ: validation.correctedPosition.z,
                                reason: validation.reason
                            });
                            
                            data.posX = validation.correctedPosition.x;
                            data.posY = validation.correctedPosition.y;
                            data.posZ = validation.correctedPosition.z;
                        } else if (validation.action === 'kick' || validation.action === 'ban') {
                            break;
                        } else if (validation.action === 'ignore') {
                            break;
                        }
                    }

                    player.position = {
                        x: typeof data.posX === 'number' && isFinite(data.posX) ? data.posX : player.position.x,
                        y: typeof data.posY === 'number' && isFinite(data.posY) ? data.posY : player.position.y,
                        z: typeof data.posZ === 'number' && isFinite(data.posZ) ? data.posZ : player.position.z
                    };
                    player.rotation = {
                        x: typeof data.rotX === 'number' && isFinite(data.rotX) ? data.rotX : 0,
                        y: typeof data.rotY === 'number' && isFinite(data.rotY) ? data.rotY : 0,
                        z: typeof data.rotZ === 'number' && isFinite(data.rotZ) ? data.rotZ : 0
                    };
                    player.velocity = {
                        x: typeof data.velX === 'number' && isFinite(data.velX) ? data.velX : 0,
                        y: typeof data.velY === 'number' && isFinite(data.velY) ? data.velY : 0,
                        z: typeof data.velZ === 'number' && isFinite(data.velZ) ? data.velZ : 0
                    };
                    player.animationId = typeof data.animationId === 'number' ? data.animationId : 0;
                    player.isGrounded = !!data.isGrounded;
                    player.isJumping = !!data.isJumping;
                    player.isSprinting = !!data.isSprinting;
                    player.isInWater = !!data.isInWater;
                    player.lastUpdate = Date.now();

                    broadcastToGame(clientGameId, {
                        type: PacketType.PLAYER_STATE,
                        odilId: clientOdilId,
                        posX: player.position.x,
                        posY: player.position.y,
                        posZ: player.position.z,
                        rotX: player.rotation.x,
                        rotY: player.rotation.y,
                        rotZ: player.rotation.z,
                        velX: player.velocity.x,
                        velY: player.velocity.y,
                        velZ: player.velocity.z,
                        animationId: player.animationId,
                        isGrounded: player.isGrounded,
                        isJumping: player.isJumping,
                        isSprinting: player.isSprinting,
                        isInWater: player.isInWater
                    }, clientOdilId);
                    break;
                }

                case PacketType.CHAT_MESSAGE: {
                    if (!clientGameId || !clientOdilId || !isConnected) break;
                    
                    const chatCheck = antiCheat.checkChatRate(clientOdilId);
                    if (!chatCheck.allowed) {
                        sendToClient(ws, {
                            type: PacketType.CHAT_MESSAGE,
                            odilId: 0,
                            username: '[Server]',
                            message: 'You are sending messages too fast!'
                        });
                        break;
                    }
                    
                    const chatMsg = (data.message || '').trim();
                    if (!chatMsg || chatMsg.length > 256) break;
                    
                    const filtered = chatMsg.replace(/[<>]/g, '');
                    
                    broadcastToGame(clientGameId, {
                        type: PacketType.CHAT_MESSAGE,
                        odilId: clientOdilId,
                        username: clientUsername,
                        message: filtered
                    });
                    break;
                }

                case PacketType.PING: {
                    sendToClient(ws, {
                        type: PacketType.PONG,
                        clientTime: data.clientTime,
                        serverTime: Date.now()
                    });
                    break;
                }

                case PacketType.DISCONNECT: {
                    console.log(`[WS] DISCONNECT from ${clientUsername} (#${clientOdilId})`);
                    isConnected = false;
                    ws.close(1000, 'Client disconnect');
                    break;
                }
            }
        } catch (err) {
            console.error('[WS] Message error:', err);
        }
    });

    ws.on('close', (code, reason) => {
        console.log(`[WS] Connection closed: ${clientUsername} (#${clientOdilId}), code=${code}`);
        if (clientGameId && clientOdilId && isConnected) {
            removePlayerFromGame(clientGameId, clientOdilId);
        }
        isConnected = false;
    });

    ws.on('error', (err) => {
        console.error(`[WS] Error for ${clientUsername}:`, err.message);
    });
});

// WebSocket heartbeat
const pingInterval = setInterval(() => {
    wss.clients.forEach((ws) => {
        if (ws.isAlive === false) return ws.terminate();
        ws.isAlive = false;
        ws.ping();
    });
}, 30000);

wss.on('close', () => clearInterval(pingInterval));

// Cleanup inactive players
setInterval(() => {
    const now = Date.now();
    gameServers.forEach((game, gameId) => {
        const toRemove = [];
        game.players.forEach((player, odilId) => {
            if (now - player.lastUpdate > 60000) toRemove.push(odilId);
        });
        toRemove.forEach(odilId => {
            const player = game.players.get(odilId);
            if (player && player.ws) player.ws.close(1000, 'Timeout');
            removePlayerFromGame(gameId, odilId);
        });
    });
    
    for (const [odilId, session] of onlineSessions.entries()) {
        if (now - session.lastActivity > SESSION_TIMEOUT) {
            onlineSessions.delete(odilId);
        }
    }
}, 15000);

// ═══════════════════════════════════════════════════════════════
// MONGOOSE SCHEMAS
// ═══════════════════════════════════════════════════════════════

const userSchema = new mongoose.Schema({
    odilId: { type: Number, unique: true },
    username: { type: String, required: true, unique: true },
    lastSeen: { type: Date, default: Date.now }
});
const User = mongoose.models.User || mongoose.model('User', userSchema);

const gameSchema = new mongoose.Schema({
    id: { type: String, unique: true, required: true },
    title: { type: String, required: true },
    description: { type: String, default: '' },
    creator: { type: String, required: true },
    creatorId: { type: Number },
    thumbnail: { type: String, default: '' },
    featured: { type: Boolean, default: false },
    category: { type: String, default: 'other' },
    visits: { type: Number, default: 0 },
    activePlayers: { type: Number, default: 0 },
    maxPlayers: { type: Number, default: 50 },
    buildData: { type: mongoose.Schema.Types.Mixed, default: null },
    createdAt: { type: Date, default: Date.now },
    updatedAt: { type: Date, default: Date.now }
});
const Game = mongoose.models.Game || mongoose.model('Game', gameSchema);

const banSchema = new mongoose.Schema({
    odilId: { type: Number },
    ip: { type: String },
    reason: { type: String },
    bannedBy: { type: Number },
    bannedAt: { type: Date, default: Date.now },
    expiresAt: { type: Date, default: null }
});
const Ban = mongoose.models.Ban || mongoose.model('Ban', banSchema);

// ═══════════════════════════════════════════════════════════════
// MONGODB CONNECTION
// ═══════════════════════════════════════════════════════════════

mongoose.connect(process.env.MONGODB_URI, {
    serverSelectionTimeoutMS: 10000,
    socketTimeoutMS: 45000,
    maxPoolSize: 10,
    minPoolSize: 2,
    retryWrites: true,
    retryReads: true
})
.then(async () => {
    console.log('[DB] MongoDB connected successfully');
    
    try { 
        await mongoose.connection.collection('users').dropIndex('email_1'); 
    } catch (e) {}
    
    const bans = await Ban.find({});
    for (const ban of bans) {
        if (ban.expiresAt && ban.expiresAt < new Date()) continue;
        if (ban.odilId) antiCheat.bannedOdilIds.add(ban.odilId);
        if (ban.ip) antiCheat.bannedIPs.add(ban.ip);
    }
    console.log(`[AC] Loaded ${antiCheat.bannedOdilIds.size} banned users, ${antiCheat.bannedIPs.size} banned IPs`);
})
.catch(err => console.error('[DB] MongoDB connection error:', err));

mongoose.connection.on('disconnected', () => {
    console.log('[DB] MongoDB disconnected, attempting reconnect...');
});

mongoose.connection.on('reconnected', () => {
    console.log('[DB] MongoDB reconnected');
});

// ═══════════════════════════════════════════════════════════════
// API ROUTES
// ═══════════════════════════════════════════════════════════════

// Presence API - Called by Vercel website
app.get('/api/presence/:id', (req, res) => {
    const odilId = parseInt(req.params.id);
    if (isNaN(odilId)) {
        return res.json({ success: false, isOnline: false, currentGame: null });
    }
    
    const presence = getUserPresence(odilId);
    res.json({
        success: true,
        isOnline: presence.isOnline,
        currentGame: presence.currentGame
    });
});

// Game servers list
app.get('/api/game/:id/servers', (req, res) => {
    const game = gameServers.get(req.params.id);
    if (!game || game.players.size === 0) {
        return res.json({ success: true, servers: [] });
    }
    
    const hostPlayer = game.players.get(game.hostOdilId);
    res.json({
        success: true,
        servers: [{
            id: req.params.id,
            name: `${hostPlayer?.username || 'Unknown'}'s Server`,
            players: game.players.size,
            maxPlayers: 50,
            hostOdilId: game.hostOdilId
        }]
    });
});

// All active games
app.get('/api/servers', (req, res) => {
    const servers = [];
    gameServers.forEach((game, gameId) => {
        if (game.players.size > 0) {
            const hostPlayer = game.players.get(game.hostOdilId);
            servers.push({
                gameId,
                players: game.players.size,
                hostUsername: hostPlayer?.username || 'Unknown',
                createdAt: game.createdAt
            });
        }
    });
    res.json({ 
        success: true, 
        servers, 
        totalPlayers: connectedClients.size,
        totalGames: gameServers.size
    });
});

// AntiCheat stats (admin endpoint - add auth in production!)
app.get('/api/admin/ac/stats', (req, res) => {
    const serverStats = antiCheat.getServerStats();
    const playerStats = [];
    antiCheat.players.forEach((player, odilId) => {
        playerStats.push(antiCheat.getStats(odilId));
    });
    res.json({ 
        success: true, 
        server: serverStats, 
        players: playerStats 
    });
});

// ═══════════════════════════════════════════════════════════════
// DOWNLOADS
// ═══════════════════════════════════════════════════════════════

app.get('/download/TuBloxSetup.exe', (req, res) => {
    const filePath = path.join(__dirname, 'public', 'download', 'TuBloxSetup.exe');
    if (!fs.existsSync(filePath)) return res.status(404).send('File not found');
    res.download(filePath, 'TuBloxSetup.exe');
});

app.get('/download/TuClient.zip', (req, res) => {
    const filePath = path.join(__dirname, 'public', 'download', 'TuClient.zip');
    if (!fs.existsSync(filePath)) return res.status(404).send('File not found');
    res.download(filePath, 'TuClient.zip');
});

app.get('/download/TuStudio.zip', (req, res) => {
    const filePath = path.join(__dirname, 'public', 'download', 'TuStudio.zip');
    if (!fs.existsSync(filePath)) return res.status(404).send('File not found');
    res.download(filePath, 'TuStudio.zip');
});


// ═══════════════════════════════════════════════════════════════
// ERROR HANDLER
// ═══════════════════════════════════════════════════════════════

app.use((err, req, res, next) => {
    console.error('[Server] Error:', err);
    res.status(500).json({ success: false, message: 'Internal server error' });
});

app.use((req, res) => {
    res.status(404).json({ success: false, message: 'Not found' });
});

// ═══════════════════════════════════════════════════════════════
// GRACEFUL SHUTDOWN
// ═══════════════════════════════════════════════════════════════

process.on('SIGTERM', async () => {
    console.log('[Server] SIGTERM received, shutting down gracefully...');
    
    connectedClients.forEach((client, odilId) => {
        if (client.ws && client.ws.readyState === WebSocket.OPEN) {
            sendToClient(client.ws, {
                type: PacketType.CHAT_MESSAGE,
                odilId: 0,
                username: '[Server]',
                message: 'Server is restarting, please reconnect in a moment...'
            });
            client.ws.close(1001, 'Server restarting');
        }
    });
    
    wss.close(() => {
        console.log('[WS] WebSocket server closed');
    });
    
    server.close(() => {
        console.log('[Server] HTTP server closed');
    });
    
    await mongoose.connection.close();
    console.log('[DB] MongoDB connection closed');
    
    process.exit(0);
});

process.on('unhandledRejection', (reason, promise) => {
    console.error('[Server] Unhandled Rejection:', reason);
});

process.on('uncaughtException', (err) => {
    console.error('[Server] Uncaught Exception:', err);
    if (!IS_RENDER) process.exit(1);
});

// ═══════════════════════════════════════════════════════════════
// START SERVER
// ═══════════════════════════════════════════════════════════════

const PORT = process.env.PORT || 3000;
server.listen(PORT, '0.0.0.0', () => {
    console.log('╔══════════════════════════════════════════════════════════╗');
    console.log(`║  TuBlox Game Server running on port ${PORT}               ║`);
    console.log(`║  WebSocket path: /ws                                    ║`);
    console.log(`║  AntiCheat: ACTIVE                                      ║`);
    console.log(`║  Keep-Alive: ${SELF_URL ? 'ACTIVE' : 'DISABLED'}                                    ║`);
    console.log('╚══════════════════════════════════════════════════════════╝');
});