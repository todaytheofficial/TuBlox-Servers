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
// RENDER.COM OPTIMIZATIONS
// ═══════════════════════════════════════════════════════════════

const IS_RENDER = !!process.env.RENDER;
const RENDER_URL = process.env.RENDER_EXTERNAL_URL;
const RENDER_HOSTNAME = process.env.RENDER_EXTERNAL_HOSTNAME;

console.log('╔══════════════════════════════════════════════════════════╗');
console.log('║           TuBlox Servers v1.0 — Starting...            ║');
console.log('║         Optimized for Render.com Free Tier             ║');
console.log('╚══════════════════════════════════════════════════════════╝');
console.log(`[Boot] Environment: ${process.env.NODE_ENV || 'development'}`);
console.log(`[Boot] Render: ${IS_RENDER ? 'YES' : 'NO'}`);
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
// KEEP ALIVE — Render Free Tier Anti-Sleep
// ═══════════════════════════════════════════════════════════════

const SELF_URL = RENDER_URL || process.env.SELF_URL;

if (SELF_URL) {
    // Ping every 14 minutes to prevent Render free tier sleep
    const keepAliveInterval = setInterval(() => {
        const https = require('https');
        const httpModule = require('http');
        const client = SELF_URL.startsWith('https') ? https : httpModule;
        
        client.get(SELF_URL + '/api/health', (res) => {
            console.log('[KeepAlive] Ping OK, status:', res.statusCode);
        }).on('error', (err) => {
            console.log('[KeepAlive] Ping failed:', err.message);
        });
    }, 14 * 60 * 1000); // 14 minutes

    // Also ping more frequently during active use
    const activeKeepAlive = setInterval(() => {
        if (connectedClients.size > 0) {
            const https = require('https');
            const httpModule = require('http');
            const client = SELF_URL.startsWith('https') ? https : httpModule;
            
            client.get(SELF_URL + '/api/health', () => {}).on('error', () => {});
        }
    }, 5 * 60 * 1000); // 5 minutes when players connected
    
    console.log(`[KeepAlive] Active — pinging ${SELF_URL} every 14min`);
} else {
    console.log('[KeepAlive] No SELF_URL set, keep-alive disabled');
}

// ═══════════════════════════════════════════════════════════════
// EXPRESS MIDDLEWARE
// ═══════════════════════════════════════════════════════════════

// Security headers (relaxed for game use)
app.use(helmet({
    contentSecurityPolicy: false,
    crossOriginEmbedderPolicy: false
}));

// Compression
app.use(compression());

// CORS — allow TuBlox frontend
app.use(cors({
    origin: [
        'https://tublox.vercel.app',
        'https://tublox.onrender.com',
        'http://localhost:3000',
        'http://localhost:5500',
        /\.vercel\.app$/,
        /\.onrender\.com$/
    ],
    credentials: true,
    methods: ['GET', 'POST', 'PUT', 'DELETE', 'PATCH', 'OPTIONS'],
    allowedHeaders: ['Content-Type', 'Authorization', 'Cookie']
}));

// Rate limiting
const apiLimiter = rateLimit({
    windowMs: 15 * 60 * 1000, // 15 min
    max: 300, // 300 requests per 15 min
    standardHeaders: true,
    legacyHeaders: false,
    message: { success: false, message: 'Too many requests, slow down!' }
});

const authLimiter = rateLimit({
    windowMs: 15 * 60 * 1000,
    max: 20,
    message: { success: false, message: 'Too many auth attempts' }
});

app.use('/api/', apiLimiter);
app.use('/api/login', authLimiter);
app.use('/api/register', authLimiter);

app.use(express.json({ limit: '10mb' }));
app.use(express.urlencoded({ extended: true }));
app.use(cookieParser());
app.use(express.static(path.join(__dirname, 'public'), {
    maxAge: '1h',
    etag: true
}));

// Request logging (minimal for performance)
app.use((req, res, next) => {
    if (req.path === '/api/health' || req.path === '/api/heartbeat') return next();
    const start = Date.now();
    res.on('finish', () => {
        const duration = Date.now() - start;
        if (duration > 1000) {
            console.log(`[SLOW] ${req.method} ${req.path} — ${duration}ms`);
        }
    });
    next();
});

// ═══════════════════════════════════════════════════════════════
// HEALTH CHECK
// ═══════════════════════════════════════════════════════════════

app.get('/api/health', (req, res) => {
    res.json({
        status: 'ok',
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
    maxPayload: 16 * 1024, // 16KB max message
    perMessageDeflate: false // Disable for lower latency
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
        sendToClient(client.ws, { type: PacketType.AC_WARN, message: reason });
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
        sendToClient(client.ws, { type: PacketType.AC_KICK, reason: `AntiCheat: ${reason}` });
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
        sendToClient(client.ws, { type: PacketType.AC_KICK, reason: `AntiCheat BAN: ${reason}` });
        setTimeout(() => {
            if (client.ws && client.ws.readyState === WebSocket.OPEN) {
                client.ws.close(1000, `AntiCheat BAN: ${reason}`);
            }
        }, 100);
    }
    if (client && client.gameId) {
        removePlayerFromGame(client.gameId, odilId);
    }
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
    
    if (isNaN(odilIdNum)) return { isOnline: false, currentGame: null };
    
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
    if (!presence.currentGame || !presence.currentGame.gameId) return presence;
    
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
                if (!rateCheck.allowed) return;
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

const counterSchema = new mongoose.Schema({
    _id: String,
    seq: { type: Number, default: 0 }
});
const Counter = mongoose.model('Counter', counterSchema);

async function getNextUserId() {
    const counter = await Counter.findByIdAndUpdate('userId', { $inc: { seq: 1 } }, { new: true, upsert: true });
    return counter.seq;
}

async function getNextPostId() {
    const counter = await Counter.findByIdAndUpdate('postId', { $inc: { seq: 1 } }, { new: true, upsert: true });
    return counter.seq;
}

async function getNextReplyId() {
    const counter = await Counter.findByIdAndUpdate('replyId', { $inc: { seq: 1 } }, { new: true, upsert: true });
    return counter.seq;
}

const userSchema = new mongoose.Schema({
    odilId: { type: Number, unique: true },
    username: { type: String, required: true, unique: true, minlength: 3, maxlength: 20, lowercase: true, trim: true },
    password: { type: String, required: true },
    createdAt: { type: Date, default: Date.now },
    lastLogin: { type: Date, default: Date.now },
    lastSeen: { type: Date, default: Date.now },
    gameData: {
        level: { type: Number, default: 1 },
        coins: { type: Number, default: 0 },
        playTime: { type: Number, default: 0 }
    }
});
const User = mongoose.model('User', userSchema);

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
const Game = mongoose.model('Game', gameSchema);

const launchTokenSchema = new mongoose.Schema({
    token: { type: String, unique: true },
    odilId: { type: Number, required: true },
    username: { type: String, required: true },
    gameId: { type: String, required: true },
    createdAt: { type: Date, default: Date.now, expires: 300 }
});
const LaunchToken = mongoose.model('LaunchToken', launchTokenSchema);

const forumPostSchema = new mongoose.Schema({
    postId: { type: Number, unique: true },
    authorId: { type: Number, required: true },
    authorName: { type: String, required: true },
    title: { type: String, required: true, maxlength: 100 },
    content: { type: String, required: true, maxlength: 5000 },
    category: { type: String, default: 'general' },
    likes: [{ type: Number }],
    views: { type: Number, default: 0 },
    replies: { type: Number, default: 0 },
    isPinned: { type: Boolean, default: false },
    isLocked: { type: Boolean, default: false },
    createdAt: { type: Date, default: Date.now },
    updatedAt: { type: Date, default: Date.now }
});
const ForumPost = mongoose.model('ForumPost', forumPostSchema);

const forumReplySchema = new mongoose.Schema({
    replyId: { type: Number, unique: true },
    postId: { type: Number, required: true },
    authorId: { type: Number, required: true },
    authorName: { type: String, required: true },
    content: { type: String, required: true, maxlength: 2000 },
    likes: [{ type: Number }],
    createdAt: { type: Date, default: Date.now }
});
const ForumReply = mongoose.model('ForumReply', forumReplySchema);

const banSchema = new mongoose.Schema({
    odilId: { type: Number },
    ip: { type: String },
    reason: { type: String },
    bannedBy: { type: Number },
    bannedAt: { type: Date, default: Date.now },
    expiresAt: { type: Date, default: null }
});
const Ban = mongoose.model('Ban', banSchema);

const whitelistSchema = new mongoose.Schema({
    odilId: { type: Number, unique: true, required: true },
    username: { type: String, required: true },
    status: { type: String, default: 'approved', enum: ['pending', 'approved', 'rejected'] },
    requestedAt: { type: Date, default: Date.now },
    approvedAt: { type: Date }
});
const Whitelist = mongoose.model('Whitelist', whitelistSchema);

// ═══════════════════════════════════════════════════════════════
// BADGES
// ═══════════════════════════════════════════════════════════════

const BADGES = {
    'Staff': {
        id: 'Staff',
        name: 'Staff',
        description: 'TuBlox Staff Member',
        icon: '/img/badges/Staff.svg',
        color: '#ff4444',
        rarity: 'legendary',
        holders: [1, 5]
    },
    'TuBloxUser': {
        id: 'TuBloxUser',
        name: 'TuBlox User',
        description: 'Verified TuBlox Player',
        icon: '/img/badges/TuBloxUser.svg',
        color: '#00c8ff',
        rarity: 'common',
        holders: null
    }
};

function getUserBadges(odilId) {
    const badges = [];
    
    for (const [badgeId, badge] of Object.entries(BADGES)) {
        if (badge.holders === null) {
            badges.push({
                id: badge.id,
                name: badge.name,
                description: badge.description,
                icon: badge.icon,
                color: badge.color,
                rarity: badge.rarity
            });
        } else if (Array.isArray(badge.holders) && badge.holders.includes(odilId)) {
            badges.push({
                id: badge.id,
                name: badge.name,
                description: badge.description,
                icon: badge.icon,
                color: badge.color,
                rarity: badge.rarity
            });
        }
    }
    
    const rarityOrder = { legendary: 0, epic: 1, rare: 2, uncommon: 3, common: 4 };
    badges.sort((a, b) => (rarityOrder[a.rarity] || 99) - (rarityOrder[b.rarity] || 99));
    
    return badges;
}

// ═══════════════════════════════════════════════════════════════
// GAME BUILD DATA
// ═══════════════════════════════════════════════════════════════

const baseplateBuildData = {
    objects: [
        { type: 'cube', position: { x: 0, y: -0.5, z: 0 }, scale: { x: 100, y: 1, z: 100 }, color: { r: 0.3, g: 0.8, b: 0.3 }, isStatic: true },
        { type: 'spawn', position: { x: 0, y: 2, z: 0 } }
    ],
    settings: { gravity: -20, skyColor: { r: 0.53, g: 0.81, b: 0.92 }, ambientColor: { r: 0.4, g: 0.4, b: 0.5 }, fogEnabled: false, spawnPoint: { x: 0, y: 2, z: 0 } },
    version: 1
};

const obbyBuildData = {
    objects: [
        { type: 'cube', position: { x: 0, y: 0, z: 0 }, scale: { x: 8, y: 1, z: 8 }, color: { r: 0.2, g: 0.6, b: 0.2 }, isStatic: true },
        { type: 'spawn', position: { x: 0, y: 2, z: 0 } },
        { type: 'cube', position: { x: 0, y: 0, z: 12 }, scale: { x: 4, y: 1, z: 4 }, color: { r: 0.9, g: 0.3, b: 0.3 }, isStatic: true },
        { type: 'cube', position: { x: 0, y: 2, z: 20 }, scale: { x: 4, y: 1, z: 4 }, color: { r: 0.9, g: 0.6, b: 0.2 }, isStatic: true },
        { type: 'cube', position: { x: 6, y: 4, z: 20 }, scale: { x: 3, y: 1, z: 3 }, color: { r: 0.9, g: 0.9, b: 0.2 }, isStatic: true },
        { type: 'cube', position: { x: 12, y: 6, z: 20 }, scale: { x: 3, y: 1, z: 3 }, color: { r: 0.2, g: 0.9, b: 0.2 }, isStatic: true },
        { type: 'cube', position: { x: 12, y: 8, z: 12 }, scale: { x: 3, y: 1, z: 3 }, color: { r: 0.2, g: 0.7, b: 0.9 }, isStatic: true },
        { type: 'cube', position: { x: 12, y: 10, z: 4 }, scale: { x: 3, y: 1, z: 3 }, color: { r: 0.5, g: 0.2, b: 0.9 }, isStatic: true },
        { type: 'cube', position: { x: 12, y: 12, z: -4 }, scale: { x: 6, y: 1, z: 6 }, color: { r: 1.0, g: 0.84, b: 0.0 }, isStatic: true }
    ],
    settings: { gravity: -25, skyColor: { r: 0.4, g: 0.6, b: 0.9 }, ambientColor: { r: 0.5, g: 0.5, b: 0.6 }, fogEnabled: false, spawnPoint: { x: 0, y: 2, z: 0 } },
    version: 1
};

const hotelBuildData = {
    objects: [
        { type: 'cube', position: { x: 0, y: 0, z: 0 }, scale: { x: 30, y: 0.5, z: 40 }, color: { r: 0.15, g: 0.1, b: 0.08 }, isStatic: true },
        { type: 'cube', position: { x: 0, y: 0.26, z: 0 }, scale: { x: 12, y: 0.02, z: 20 }, color: { r: 0.6, g: 0.1, b: 0.15 }, isStatic: true },
        { type: 'cube', position: { x: 0, y: 10, z: 0 }, scale: { x: 30, y: 0.5, z: 40 }, color: { r: 0.95, g: 0.93, b: 0.88 }, isStatic: true },
        { type: 'cube', position: { x: -15, y: 5, z: 0 }, scale: { x: 0.5, y: 10, z: 40 }, color: { r: 0.85, g: 0.8, b: 0.7 }, isStatic: true },
        { type: 'cube', position: { x: 15, y: 5, z: 0 }, scale: { x: 0.5, y: 10, z: 40 }, color: { r: 0.85, g: 0.8, b: 0.7 }, isStatic: true },
        { type: 'cube', position: { x: 0, y: 5, z: -20 }, scale: { x: 30, y: 10, z: 0.5 }, color: { r: 0.85, g: 0.8, b: 0.7 }, isStatic: true },
        { type: 'cube', position: { x: -10, y: 5, z: 20 }, scale: { x: 10, y: 10, z: 0.5 }, color: { r: 0.85, g: 0.8, b: 0.7 }, isStatic: true },
        { type: 'cube', position: { x: 10, y: 5, z: 20 }, scale: { x: 10, y: 10, z: 0.5 }, color: { r: 0.85, g: 0.8, b: 0.7 }, isStatic: true },
        { type: 'cube', position: { x: 0, y: 1.5, z: -15 }, scale: { x: 10, y: 3, z: 2 }, color: { r: 0.3, g: 0.2, b: 0.15 }, isStatic: true },
        { type: 'cube', position: { x: -10, y: 0.8, z: 5 }, scale: { x: 5, y: 1.6, z: 2 }, color: { r: 0.2, g: 0.15, b: 0.4 }, isStatic: true },
        { type: 'cube', position: { x: 10, y: 0.8, z: 5 }, scale: { x: 5, y: 1.6, z: 2 }, color: { r: 0.2, g: 0.15, b: 0.4 }, isStatic: true },
        { type: 'spawn', position: { x: 0, y: 2, z: 15 } }
    ],
    settings: { gravity: -20, skyColor: { r: 0.1, g: 0.1, b: 0.15 }, ambientColor: { r: 0.6, g: 0.55, b: 0.5 }, fogEnabled: false, spawnPoint: { x: 0, y: 2, z: 15 } },
    version: 1
};

// ═══════════════════════════════════════════════════════════════
// CONSTANTS
// ═══════════════════════════════════════════════════════════════

const ADMIN_IDS = [1];
const AUTO_APPROVE = true;

// ═══════════════════════════════════════════════════════════════
// MONGODB CONNECTION
// ═══════════════════════════════════════════════════════════════

mongoose.connect(process.env.MONGODB_URI, {
    // Render.com optimizations
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
    
    // Load bans
    const bans = await Ban.find({});
    for (const ban of bans) {
        if (ban.expiresAt && ban.expiresAt < new Date()) continue;
        if (ban.odilId) antiCheat.bannedOdilIds.add(ban.odilId);
        if (ban.ip) antiCheat.bannedIPs.add(ban.ip);
    }
    console.log(`[AC] Loaded ${antiCheat.bannedOdilIds.size} banned users, ${antiCheat.bannedIPs.size} banned IPs`);
    
    // Create/update games
    await Game.deleteMany({});
    const games = [
        { id: 'baseplate', title: 'Baseplate', description: 'A simple green baseplate. Perfect for hanging out with friends!', creator: 'Today_Idk', creatorId: 1, featured: true, category: 'sandbox', visits: 1, maxPlayers: 50, buildData: baseplateBuildData },
        { id: 'obby', title: 'Obby', description: 'Jump through colorful platforms and reach the golden finish!', creator: 'Today_Idk', creatorId: 1, featured: true, category: 'obby', visits: 1, maxPlayers: 30, buildData: obbyBuildData },
        { id: 'hotel', title: 'Hotel', description: 'A beautiful hotel lobby. Relax and meet new people!', creator: 'Today_Idk', creatorId: 1, featured: true, category: 'roleplay', visits: 1, maxPlayers: 40, buildData: hotelBuildData }
    ];
    await Game.insertMany(games);
    console.log(`[DB] Created ${games.length} games`);
})
.catch(err => console.error('[DB] MongoDB connection error:', err));

// Handle connection events
mongoose.connection.on('disconnected', () => {
    console.log('[DB] MongoDB disconnected, attempting reconnect...');
});

mongoose.connection.on('reconnected', () => {
    console.log('[DB] MongoDB reconnected');
});

// ═══════════════════════════════════════════════════════════════
// AUTH MIDDLEWARE
// ═══════════════════════════════════════════════════════════════

const auth = async (req, res, next) => {
    try {
        const token = req.cookies.token;
        if (!token) return res.redirect('/auth');
        const decoded = jwt.verify(token, process.env.JWT_SECRET);
        const user = await User.findById(decoded.id).select('-password');
        if (!user) { res.clearCookie('token'); return res.redirect('/auth'); }
        req.user = user;
        next();
    } catch (err) {
        res.clearCookie('token');
        res.redirect('/auth');
    }
};

const authAPI = async (req, res, next) => {
    try {
        const token = req.cookies.token;
        if (!token) return res.status(401).json({ success: false, message: 'Not authorized' });
        const decoded = jwt.verify(token, process.env.JWT_SECRET);
        const user = await User.findById(decoded.id).select('-password');
        if (!user) { res.clearCookie('token'); return res.status(401).json({ success: false, message: 'Not authorized' }); }
        req.user = user;
        onlineSessions.set(user.odilId, { lastActivity: Date.now() });
        next();
    } catch (err) {
        res.clearCookie('token');
        res.status(401).json({ success: false, message: 'Not authorized' });
    }
};

const adminAPI = async (req, res, next) => {
    await authAPI(req, res, () => {
        if (!antiCheat.adminIds.has(req.user.odilId)) {
            return res.status(403).json({ success: false, message: 'Admin access required' });
        }
        next();
    });
};

// ═══════════════════════════════════════════════════════════════
// PAGES
// ═══════════════════════════════════════════════════════════════

app.get('/', (req, res) => {
    try {
        const token = req.cookies.token;
        if (token && jwt.verify(token, process.env.JWT_SECRET)) return res.redirect('/home');
    } catch (e) { res.clearCookie('token'); }
    res.sendFile(path.join(__dirname, 'pages', 'landing.html'));
});

app.get('/auth', (req, res) => {
    try {
        const token = req.cookies.token;
        if (token && jwt.verify(token, process.env.JWT_SECRET)) return res.redirect('/home');
    } catch (e) { res.clearCookie('token'); }
    res.sendFile(path.join(__dirname, 'pages', 'auth.html'));
});

app.get('/home', auth, (req, res) => res.sendFile(path.join(__dirname, 'pages', 'home.html')));
app.get('/games', auth, (req, res) => res.sendFile(path.join(__dirname, 'pages', 'games.html')));
app.get('/game/:id', auth, (req, res) => res.sendFile(path.join(__dirname, 'pages', 'game.html')));
app.get('/users', (req, res) => res.sendFile(path.join(__dirname, 'pages', 'users.html')));
app.get('/user/:id', (req, res) => res.sendFile(path.join(__dirname, 'pages', 'profile.html')));
app.get('/TuForums', (req, res) => res.sendFile(path.join(__dirname, 'pages', 'forum.html')));
app.get('/TuForums/:ownerId', (req, res) => res.sendFile(path.join(__dirname, 'pages', 'forum-user.html')));
app.get('/TuForums/:ownerId/:postId', (req, res) => res.sendFile(path.join(__dirname, 'pages', 'forum-post.html')));
app.get('/whitelist', (req, res) => res.sendFile(path.join(__dirname, 'pages', 'whitelist.html')));

// ═══════════════════════════════════════════════════════════════
// API - WHITELIST
// ═══════════════════════════════════════════════════════════════

app.get('/api/whitelist/count', async (req, res) => {
    try {
        const count = await Whitelist.countDocuments({ status: 'approved' });
        res.json({ success: true, count });
    } catch (err) {
        res.status(500).json({ success: false });
    }
});

app.get('/api/whitelist/me', authAPI, async (req, res) => {
    try {
        const entry = await Whitelist.findOne({ odilId: req.user.odilId });
        res.json({
            success: true,
            whitelisted: entry?.status === 'approved',
            pending: entry?.status === 'pending',
            status: entry?.status || null
        });
    } catch (err) {
        res.status(500).json({ success: false });
    }
});

app.post('/api/whitelist/request', authAPI, async (req, res) => {
    try {
        const existing = await Whitelist.findOne({ odilId: req.user.odilId });
        
        if (existing) {
            if (existing.status === 'approved') return res.json({ success: true, whitelisted: true, autoApproved: false });
            if (existing.status === 'pending') return res.json({ success: true, pending: true });
            if (existing.status === 'rejected') return res.status(400).json({ success: false, message: 'Request was rejected' });
        }
        
        const entry = new Whitelist({
            odilId: req.user.odilId,
            username: req.user.username,
            status: AUTO_APPROVE ? 'approved' : 'pending',
            approvedAt: AUTO_APPROVE ? new Date() : null
        });
        await entry.save();
        
        console.log(`[Whitelist] ${AUTO_APPROVE ? 'Auto-approved' : 'Request'}: #${req.user.odilId} (${req.user.username})`);
        
        res.json({ 
            success: true, 
            autoApproved: AUTO_APPROVE,
            whitelisted: AUTO_APPROVE,
            pending: !AUTO_APPROVE
        });
    } catch (err) {
        console.error('[Whitelist] Request error:', err);
        res.status(500).json({ success: false, message: 'Server error' });
    }
});

app.get('/api/whitelist/check/:id', async (req, res) => {
    try {
        const odilId = parseInt(req.params.id);
        const entry = await Whitelist.findOne({ odilId, status: 'approved' });
        res.json({ success: true, whitelisted: !!entry });
    } catch (err) {
        res.status(500).json({ success: false });
    }
});

app.get('/api/whitelist', authAPI, async (req, res) => {
    try {
        if (!ADMIN_IDS.includes(req.user.odilId)) return res.status(403).json({ success: false, message: 'Admin only' });
        const { status } = req.query;
        const query = status ? { status } : {};
        const entries = await Whitelist.find(query).sort({ requestedAt: -1 });
        res.json({ success: true, entries, count: entries.length });
    } catch (err) {
        res.status(500).json({ success: false });
    }
});

app.patch('/api/whitelist/:id', authAPI, async (req, res) => {
    try {
        if (!ADMIN_IDS.includes(req.user.odilId)) return res.status(403).json({ success: false, message: 'Admin only' });
        
        const odilId = parseInt(req.params.id);
        const { status } = req.body;
        
        if (!['approved', 'rejected'].includes(status)) return res.status(400).json({ success: false, message: 'Invalid status' });
        
        const entry = await Whitelist.findOneAndUpdate(
            { odilId },
            { status, approvedAt: status === 'approved' ? new Date() : null },
            { new: true }
        );
        
        if (!entry) return res.status(404).json({ success: false, message: 'Not found' });
        
        res.json({ success: true, entry });
    } catch (err) {
        res.status(500).json({ success: false });
    }
});

app.delete('/api/whitelist/:id', authAPI, async (req, res) => {
    try {
        if (!ADMIN_IDS.includes(req.user.odilId)) return res.status(403).json({ success: false, message: 'Admin only' });
        
        const odilId = parseInt(req.params.id);
        const entry = await Whitelist.findOneAndDelete({ odilId });
        if (!entry) return res.status(404).json({ success: false, message: 'Not found' });
        
        res.json({ success: true });
    } catch (err) {
        res.status(500).json({ success: false });
    }
});

// ═══════════════════════════════════════════════════════════════
// API - ANTICHEAT ADMIN
// ═══════════════════════════════════════════════════════════════

app.get('/api/admin/ac/stats', adminAPI, (req, res) => {
    const serverStats = antiCheat.getServerStats();
    const playerStats = [];
    antiCheat.players.forEach((player, odilId) => {
        playerStats.push(antiCheat.getStats(odilId));
    });
    res.json({ success: true, server: serverStats, players: playerStats });
});

app.post('/api/admin/ac/kick', adminAPI, async (req, res) => {
    const { odilId, reason } = req.body;
    if (!odilId) return res.status(400).json({ success: false, message: 'odilId required' });
    antiCheat.kickPlayer(odilId, reason || 'Kicked by admin');
    res.json({ success: true });
});

app.post('/api/admin/ac/ban', adminAPI, async (req, res) => {
    const { odilId, reason, duration } = req.body;
    if (!odilId) return res.status(400).json({ success: false, message: 'odilId required' });
    
    const player = antiCheat.players.get(odilId);
    const ip = player?.ip;
    
    antiCheat.banPlayer(odilId, reason || 'Banned by admin');
    
    const ban = new Ban({
        odilId,
        ip,
        reason: reason || 'Banned by admin',
        bannedBy: req.user.odilId,
        expiresAt: duration ? new Date(Date.now() + duration * 1000) : null
    });
    await ban.save();
    
    res.json({ success: true });
});

app.post('/api/admin/ac/unban', adminAPI, async (req, res) => {
    const { odilId, ip } = req.body;
    
    if (odilId) {
        antiCheat.unbanPlayer(odilId);
        await Ban.deleteMany({ odilId });
    }
    if (ip) {
        antiCheat.unbanIP(ip);
        await Ban.deleteMany({ ip });
    }
    
    res.json({ success: true });
});

app.post('/api/admin/ac/freeze', adminAPI, (req, res) => {
    const { odilId, freeze } = req.body;
    if (!odilId) return res.status(400).json({ success: false, message: 'odilId required' });
    antiCheat.freezePlayer(odilId, freeze !== false);
    res.json({ success: true });
});

app.post('/api/admin/ac/reset', adminAPI, (req, res) => {
    const { odilId } = req.body;
    if (!odilId) return res.status(400).json({ success: false, message: 'odilId required' });
    antiCheat.resetPlayer(odilId);
    res.json({ success: true });
});

// ═══════════════════════════════════════════════════════════════
// API - DEBUG
// ═══════════════════════════════════════════════════════════════

app.get('/api/debug/presence/:id', async (req, res) => {
    const odilId = parseInt(req.params.id);
    const sessions = [];
    for (const [id, s] of onlineSessions.entries()) {
        sessions.push({ odilId: id, lastActivity: s.lastActivity, ageSeconds: Math.floor((Date.now() - s.lastActivity) / 1000) });
    }
    const presence = getUserPresence(odilId);
    const enriched = await enrichPresenceWithGameInfo({ ...presence });
    res.json({ requestedOdilId: odilId, onlineSessionsCount: onlineSessions.size, onlineSessions: sessions, presence, enrichedPresence: enriched });
});

app.post('/api/heartbeat', authAPI, (req, res) => {
    res.json({ success: true, timestamp: Date.now() });
});

app.get('/api/debug/ws', (req, res) => {
    const wsClients = [];
    wss.clients.forEach((ws, i) => {
        wsClients.push({ index: i, readyState: ws.readyState, isAlive: ws.isAlive });
    });
    res.json({ wssClientsCount: wss.clients.size, wsClients, connectedClientsCount: connectedClients.size, gameServersCount: gameServers.size });
});

// ═══════════════════════════════════════════════════════════════
// API - USER
// ═══════════════════════════════════════════════════════════════

app.get('/api/user', authAPI, (req, res) => {
    const presence = getUserPresence(req.user.odilId);
    const badges = getUserBadges(req.user.odilId);
    
    res.json({ 
        success: true, 
        user: { 
            id: req.user._id, 
            odilId: req.user.odilId, 
            username: req.user.username, 
            createdAt: req.user.createdAt,
            lastSeen: req.user.lastSeen,
            isOnline: presence.isOnline,
            currentGame: presence.currentGame,
            gameData: req.user.gameData,
            isAdmin: antiCheat.adminIds.has(req.user.odilId),
            badges: badges
        } 
    });
});

app.get('/api/users', async (req, res) => {
    try {
        const users = await User.find().select('odilId username gameData createdAt lastSeen').sort({ createdAt: -1 }).limit(100);
        const usersWithPresence = users.map(u => {
            const presence = getUserPresence(u.odilId);
            return { ...u.toObject(), isOnline: presence.isOnline, currentGame: presence.currentGame };
        });
        usersWithPresence.sort((a, b) => {
            const aScore = a.currentGame ? 2 : (a.isOnline ? 1 : 0);
            const bScore = b.currentGame ? 2 : (b.isOnline ? 1 : 0);
            return bScore - aScore;
        });
        res.json({ success: true, users: usersWithPresence });
    } catch (err) {
        res.status(500).json({ success: false, message: 'Server error' });
    }
});

app.get('/api/user/:id', async (req, res) => {
    try {
        const odilId = parseInt(req.params.id);
        if (isNaN(odilId)) return res.status(400).json({ success: false, message: 'Invalid user ID' });
        
        const user = await User.findOne({ odilId }).select('odilId username gameData createdAt lastSeen lastLogin');
        if (!user) return res.status(404).json({ success: false, message: 'User not found' });
        
        const presence = getUserPresence(odilId);
        let enrichedPresence = { ...presence };
        if (presence.currentGame) {
            enrichedPresence = await enrichPresenceWithGameInfo(enrichedPresence);
        }
        
        const badges = getUserBadges(odilId);
        
        res.json({ 
            success: true, 
            user: {
                odilId: user.odilId,
                username: user.username,
                gameData: user.gameData,
                createdAt: user.createdAt,
                isOnline: enrichedPresence.isOnline,
                currentGame: enrichedPresence.currentGame,
                lastSeen: enrichedPresence.isOnline ? null : (user.lastSeen || user.lastLogin || user.createdAt),
                isAdmin: antiCheat.adminIds.has(odilId),
                badges: badges
            }
        });
    } catch (err) { 
        console.error('[API] User error:', err);
        res.status(500).json({ success: false, message: 'Server error' }); 
    }
});

// ═══════════════════════════════════════════════════════════════
// API - BADGES
// ═══════════════════════════════════════════════════════════════

app.get('/api/badges', (req, res) => {
    const allBadges = Object.values(BADGES).map(b => ({
        id: b.id,
        name: b.name,
        description: b.description,
        icon: b.icon,
        color: b.color,
        rarity: b.rarity,
        isExclusive: b.holders !== null
    }));
    res.json({ success: true, badges: allBadges });
});

app.get('/api/user/:id/badges', async (req, res) => {
    try {
        const odilId = parseInt(req.params.id);
        if (isNaN(odilId)) return res.status(400).json({ success: false, message: 'Invalid user ID' });
        
        const user = await User.findOne({ odilId }).select('odilId username');
        if (!user) return res.status(404).json({ success: false, message: 'User not found' });
        
        const badges = getUserBadges(odilId);
        res.json({ success: true, badges, username: user.username, odilId: user.odilId });
    } catch (err) {
        res.status(500).json({ success: false, message: 'Server error' });
    }
});

// ═══════════════════════════════════════════════════════════════
// API - AUTH
// ═══════════════════════════════════════════════════════════════

app.post('/api/register', async (req, res) => {
    try {
        const { username, password } = req.body;
        if (!username || !password) return res.status(400).json({ success: false, message: 'All fields required' });
        
        const cleanUsername = username.toLowerCase().trim();
        if (cleanUsername.length < 3 || cleanUsername.length > 20) return res.status(400).json({ success: false, message: 'Username must be 3-20 characters' });
        if (!/^[a-z0-9_]+$/.test(cleanUsername)) return res.status(400).json({ success: false, message: 'Username can only contain letters, numbers and underscore' });
        if (password.length < 6) return res.status(400).json({ success: false, message: 'Password must be at least 6 characters' });
        
        const exists = await User.findOne({ username: cleanUsername });
        if (exists) return res.status(400).json({ success: false, message: 'Username already taken' });
        
        const odilId = await getNextUserId();
        const hash = await bcrypt.hash(password, 12);
        const user = new User({ username: cleanUsername, password: hash, odilId, lastSeen: new Date() });
        await user.save();
        
        const token = jwt.sign({ id: user._id }, process.env.JWT_SECRET, { expiresIn: '7d' });
        res.cookie('token', token, { 
            httpOnly: true, 
            maxAge: 7 * 24 * 60 * 60 * 1000, 
            sameSite: IS_RENDER ? 'none' : 'strict',
            secure: IS_RENDER
        });
        res.json({ success: true, odilId });
    } catch (err) {
        console.error(err);
        res.status(500).json({ success: false, message: 'Server error' });
    }
});

app.post('/api/login', async (req, res) => {
    try {
        const { username, password } = req.body;
        if (!username || !password) return res.status(400).json({ success: false, message: 'All fields required' });
        
        const cleanUsername = username.toLowerCase().trim();
        const user = await User.findOne({ username: cleanUsername });
        if (!user) return res.status(400).json({ success: false, message: 'Invalid username or password' });
        
        if (antiCheat.bannedOdilIds.has(user.odilId)) {
            return res.status(403).json({ success: false, message: 'Your account is banned' });
        }
        
        const valid = await bcrypt.compare(password, user.password);
        if (!valid) return res.status(400).json({ success: false, message: 'Invalid username or password' });
        
        user.lastLogin = new Date();
        user.lastSeen = new Date();
        await user.save();
        
        const token = jwt.sign({ id: user._id }, process.env.JWT_SECRET, { expiresIn: '7d' });
        res.cookie('token', token, { 
            httpOnly: true, 
            maxAge: 7 * 24 * 60 * 60 * 1000, 
            sameSite: IS_RENDER ? 'none' : 'strict',
            secure: IS_RENDER
        });
        res.json({ success: true });
    } catch (err) {
        console.error(err);
        res.status(500).json({ success: false, message: 'Server error' });
    }
});

app.post('/api/logout', async (req, res) => {
    try {
        const token = req.cookies.token;
        if (token) {
            const decoded = jwt.verify(token, process.env.JWT_SECRET);
            await User.findByIdAndUpdate(decoded.id, { lastSeen: new Date() });
        }
    } catch (e) {}
    res.clearCookie('token');
    res.json({ success: true });
});

// ═══════════════════════════════════════════════════════════════
// API - GAMES
// ═══════════════════════════════════════════════════════════════

app.get('/api/games', async (req, res) => {
    try {
        const { featured, category, page = 1, limit = 3 } = req.query;
        const pageNum = Math.max(1, parseInt(page) || 1);
        const limitNum = Math.min(12, Math.max(1, parseInt(limit) || 3));
        const skip = (pageNum - 1) * limitNum;
        
        let query = {};
        if (featured === 'true') query.featured = true;
        if (category && category !== 'all') query.category = category;
        
        const totalGames = await Game.countDocuments(query);
        const totalPages = Math.ceil(totalGames / limitNum);
        
        const games = await Game.find(query).select('-buildData').sort({ featured: -1, visits: -1 }).skip(skip).limit(limitNum);
        
        const gamesWithPlayers = games.map(g => {
            const gameServer = gameServers.get(g.id);
            return { ...g.toObject(), activePlayers: gameServer ? gameServer.players.size : 0 };
        });
        
        res.json({ success: true, games: gamesWithPlayers, pagination: { currentPage: pageNum, totalPages, totalGames, gamesPerPage: limitNum, hasNextPage: pageNum < totalPages, hasPrevPage: pageNum > 1 } });
    } catch (err) {
        console.error('[API] Games error:', err);
        res.status(500).json({ success: false, message: 'Server error' });
    }
});

app.get('/api/game/:id', async (req, res) => {
    try {
        const game = await Game.findOne({ id: req.params.id }).select('-buildData');
        if (!game) return res.status(404).json({ success: false, message: 'Game not found' });
        const gameServer = gameServers.get(req.params.id);
        res.json({ success: true, game: { ...game.toObject(), activePlayers: gameServer ? gameServer.players.size : 0 } });
    } catch (err) { res.status(500).json({ success: false, message: 'Server error' }); }
});

app.get('/api/game/:id/servers', async (req, res) => {
    try {
        const game = gameServers.get(req.params.id);
        if (!game || game.players.size === 0) return res.json({ success: true, servers: [] });
        const hostPlayer = game.players.get(game.hostOdilId);
        res.json({ success: true, servers: [{ id: req.params.id, name: `${hostPlayer?.username || 'Unknown'}'s Server`, players: game.players.size, maxPlayers: 50, hostOdilId: game.hostOdilId }] });
    } catch (err) { res.status(500).json({ success: false, message: 'Server error' }); }
});

app.post('/api/game/launch', authAPI, async (req, res) => {
    try {
        const { gameId } = req.body;
        const game = await Game.findOne({ id: gameId });
        if (!game) return res.status(404).json({ success: false, message: 'Game not found' });
        
        if (antiCheat.bannedOdilIds.has(req.user.odilId)) {
            return res.status(403).json({ success: false, message: 'You are banned from playing' });
        }
        
        game.visits += 1;
        await game.save();
        
        const launchToken = crypto.randomBytes(32).toString('hex');
        await LaunchToken.create({ token: launchToken, odilId: req.user.odilId, username: req.user.username, gameId: game.id });
        
        // Use Render hostname
        const wsHost = RENDER_HOSTNAME || process.env.WS_HOST || 'tublox-servers.onrender.com';
        res.json({ success: true, token: launchToken, wsHost, wsPort: 443, gameId: game.id });
    } catch (err) {
        console.error(err);
        res.status(500).json({ success: false, message: 'Server error' });
    }
});

app.get('/api/game/validate/:token', async (req, res) => {
    try {
        const launchData = await LaunchToken.findOne({ token: req.params.token });
        if (!launchData) return res.status(404).json({ success: false, message: 'Invalid or expired token' });
        
        if (antiCheat.bannedOdilIds.has(launchData.odilId)) {
            await LaunchToken.deleteOne({ token: req.params.token });
            return res.status(403).json({ success: false, message: 'You are banned' });
        }
        
        const game = await Game.findOne({ id: launchData.gameId });
        await LaunchToken.deleteOne({ token: req.params.token });
        
        const wsHost = RENDER_HOSTNAME || process.env.WS_HOST || 'tublox-servers.onrender.com';
        res.json({ 
            success: true, 
            odilId: launchData.odilId, 
            username: launchData.username, 
            gameId: launchData.gameId, 
            wsHost, 
            wsPort: 443, 
            buildData: game?.buildData || baseplateBuildData,
            gameName: game?.title || launchData.gameId,
            creatorName: game?.creator || 'Unknown'
        });
    } catch (err) {
        console.error('[Validate] Error:', err);
        res.status(500).json({ success: false, message: 'Server error' });
    }
});

// ═══════════════════════════════════════════════════════════════
// API - FORUM
// ═══════════════════════════════════════════════════════════════

const FORUM_CATEGORIES = [
    { id: 'general', name: 'General', description: 'General discussion' },
    { id: 'games', name: 'Games', description: 'Talk about games' },
    { id: 'creations', name: 'Creations', description: 'Share your creations' },
    { id: 'help', name: 'Help', description: 'Get help from community' },
    { id: 'suggestions', name: 'Suggestions', description: 'Suggest new features' },
    { id: 'offtopic', name: 'Off-Topic', description: 'Random discussions' }
];

app.get('/api/forum/categories', (req, res) => {
    res.json({ success: true, categories: FORUM_CATEGORIES });
});

app.get('/api/forum/posts', async (req, res) => {
    try {
        const { page = 1, limit = 15, category, sort = 'newest', search } = req.query;
        const pageNum = Math.max(1, parseInt(page) || 1);
        const limitNum = Math.min(50, Math.max(1, parseInt(limit) || 15));
        const skip = (pageNum - 1) * limitNum;
        
        let query = {};
        if (category && category !== 'all') query.category = category;
        if (search) query.$or = [{ title: { $regex: search, $options: 'i' } }, { content: { $regex: search, $options: 'i' } }];
        
        let sortOption = { isPinned: -1 };
        switch (sort) {
            case 'newest': sortOption.createdAt = -1; break;
            case 'oldest': sortOption.createdAt = 1; break;
            case 'popular': sortOption.views = -1; break;
            case 'mostliked': sortOption = { isPinned: -1, likes: -1 }; break;
            case 'mostreplies': sortOption.replies = -1; break;
            default: sortOption.createdAt = -1;
        }
        
        const totalPosts = await ForumPost.countDocuments(query);
        const totalPages = Math.ceil(totalPosts / limitNum);
        const posts = await ForumPost.find(query).sort(sortOption).skip(skip).limit(limitNum).lean();
        
        res.json({ success: true, posts, pagination: { currentPage: pageNum, totalPages, totalPosts, hasNextPage: pageNum < totalPages, hasPrevPage: pageNum > 1 } });
    } catch (err) {
        console.error('[Forum] Get posts error:', err);
        res.status(500).json({ success: false, message: 'Server error' });
    }
});

app.get('/api/forum/user/:ownerId/posts', async (req, res) => {
    try {
        const { page = 1, limit = 15 } = req.query;
        const pageNum = Math.max(1, parseInt(page) || 1);
        const limitNum = Math.min(50, Math.max(1, parseInt(limit) || 15));
        const skip = (pageNum - 1) * limitNum;
        const authorId = parseInt(req.params.ownerId);
        
        const user = await User.findOne({ odilId: authorId }).select('username odilId');
        if (!user) return res.status(404).json({ success: false, message: 'User not found' });
        
        const totalPosts = await ForumPost.countDocuments({ authorId });
        const totalPages = Math.ceil(totalPosts / limitNum);
        const posts = await ForumPost.find({ authorId }).sort({ createdAt: -1 }).skip(skip).limit(limitNum).lean();
        
        res.json({ success: true, user: { username: user.username, odilId: user.odilId }, posts, pagination: { currentPage: pageNum, totalPages, totalPosts, hasNextPage: pageNum < totalPages, hasPrevPage: pageNum > 1 } });
    } catch (err) {
        res.status(500).json({ success: false, message: 'Server error' });
    }
});

app.get('/api/forum/post/:ownerId/:postId', async (req, res) => {
    try {
        const post = await ForumPost.findOne({ postId: parseInt(req.params.postId), authorId: parseInt(req.params.ownerId) });
        if (!post) return res.status(404).json({ success: false, message: 'Post not found' });
        
        post.views += 1;
        await post.save();
        
        const replies = await ForumReply.find({ postId: post.postId }).sort({ createdAt: 1 }).lean();
        res.json({ success: true, post, replies });
    } catch (err) {
        res.status(500).json({ success: false, message: 'Server error' });
    }
});

app.post('/api/forum/posts', authAPI, async (req, res) => {
    try {
        if (antiCheat.bannedOdilIds.has(req.user.odilId)) return res.status(403).json({ success: false, message: 'You are banned' });
        
        const { title, content, category } = req.body;
        if (!title || !content) return res.status(400).json({ success: false, message: 'Title and content required' });
        if (title.length > 100) return res.status(400).json({ success: false, message: 'Title too long (max 100)' });
        if (content.length > 5000) return res.status(400).json({ success: false, message: 'Content too long (max 5000)' });
        
        const validCategory = FORUM_CATEGORIES.find(c => c.id === category);
        const postId = await getNextPostId();
        
        const post = new ForumPost({ postId, authorId: req.user.odilId, authorName: req.user.username, title: title.trim(), content: content.trim(), category: validCategory ? category : 'general' });
        await post.save();
        
        res.json({ success: true, post, url: `/TuForums/${req.user.odilId}/${postId}` });
    } catch (err) {
        res.status(500).json({ success: false, message: 'Server error' });
    }
});

app.post('/api/forum/post/:postId/reply', authAPI, async (req, res) => {
    try {
        if (antiCheat.bannedOdilIds.has(req.user.odilId)) return res.status(403).json({ success: false, message: 'You are banned' });
        
        const { content } = req.body;
        if (!content || content.trim().length === 0) return res.status(400).json({ success: false, message: 'Content required' });
        if (content.length > 2000) return res.status(400).json({ success: false, message: 'Reply too long (max 2000)' });
        
        const post = await ForumPost.findOne({ postId: parseInt(req.params.postId) });
        if (!post) return res.status(404).json({ success: false, message: 'Post not found' });
        if (post.isLocked) return res.status(403).json({ success: false, message: 'Post is locked' });
        
        const replyId = await getNextReplyId();
        const reply = new ForumReply({ replyId, postId: post.postId, authorId: req.user.odilId, authorName: req.user.username, content: content.trim() });
        await reply.save();
        
        post.replies += 1;
        post.updatedAt = new Date();
        await post.save();
        
        res.json({ success: true, reply });
    } catch (err) {
        res.status(500).json({ success: false, message: 'Server error' });
    }
});

app.post('/api/forum/post/:postId/like', authAPI, async (req, res) => {
    try {
        const post = await ForumPost.findOne({ postId: parseInt(req.params.postId) });
        if (!post) return res.status(404).json({ success: false, message: 'Post not found' });
        
        const userId = req.user.odilId;
        const hasLiked = post.likes.includes(userId);
        
        if (hasLiked) post.likes = post.likes.filter(id => id !== userId);
        else post.likes.push(userId);
        
        await post.save();
        res.json({ success: true, liked: !hasLiked, likesCount: post.likes.length });
    } catch (err) {
        res.status(500).json({ success: false, message: 'Server error' });
    }
});

app.post('/api/forum/reply/:replyId/like', authAPI, async (req, res) => {
    try {
        const reply = await ForumReply.findOne({ replyId: parseInt(req.params.replyId) });
        if (!reply) return res.status(404).json({ success: false, message: 'Reply not found' });
        
        const userId = req.user.odilId;
        const hasLiked = reply.likes.includes(userId);
        
        if (hasLiked) reply.likes = reply.likes.filter(id => id !== userId);
        else reply.likes.push(userId);
        
        await reply.save();
        res.json({ success: true, liked: !hasLiked, likesCount: reply.likes.length });
    } catch (err) {
        res.status(500).json({ success: false, message: 'Server error' });
    }
});

app.delete('/api/forum/post/:postId', authAPI, async (req, res) => {
    try {
        const post = await ForumPost.findOne({ postId: parseInt(req.params.postId) });
        if (!post) return res.status(404).json({ success: false, message: 'Post not found' });
        
        if (post.authorId !== req.user.odilId && !antiCheat.adminIds.has(req.user.odilId)) {
            return res.status(403).json({ success: false, message: 'Not authorized' });
        }
        
        await ForumReply.deleteMany({ postId: post.postId });
        await post.deleteOne();
        
        res.json({ success: true });
    } catch (err) {
        res.status(500).json({ success: false, message: 'Server error' });
    }
});

// ═══════════════════════════════════════════════════════════════
// API - VERSION
// ═══════════════════════════════════════════════════════════════

app.get('/api/version', (req, res) => {
    const serverUrl = RENDER_URL || 'https://tublox-servers.onrender.com';
    res.json({
        version: "0.5.1",
        downloadUrl: `${serverUrl}/download/TuClient.zip`,
        message: "Patch 0.5.1 - Fix"
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

// ═══════════════════════════════════════════════════════════════
// ERROR HANDLER
// ═══════════════════════════════════════════════════════════════

app.use((err, req, res, next) => {
    console.error('[Server] Error:', err);
    res.status(500).json({ success: false, message: 'Internal server error' });
});

// Catch-all for unmatched routes
app.use((req, res) => {
    res.status(404).json({ success: false, message: 'Not found' });
});

// ═══════════════════════════════════════════════════════════════
// GRACEFUL SHUTDOWN
// ═══════════════════════════════════════════════════════════════

process.on('SIGTERM', async () => {
    console.log('[Server] SIGTERM received, shutting down gracefully...');
    
    // Notify all connected players
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
    
    // Close WebSocket server
    wss.close(() => {
        console.log('[WS] WebSocket server closed');
    });
    
    // Close HTTP server
    server.close(() => {
        console.log('[Server] HTTP server closed');
    });
    
    // Close MongoDB
    await mongoose.connection.close();
    console.log('[DB] MongoDB connection closed');
    
    process.exit(0);
});

process.on('unhandledRejection', (reason, promise) => {
    console.error('[Server] Unhandled Rejection:', reason);
});

process.on('uncaughtException', (err) => {
    console.error('[Server] Uncaught Exception:', err);
    // Don't exit on Render, let it recover
    if (!IS_RENDER) process.exit(1);
});

// ═══════════════════════════════════════════════════════════════
// START SERVER
// ═══════════════════════════════════════════════════════════════

const PORT = process.env.PORT || 3000;
server.listen(PORT, '0.0.0.0', () => {
    console.log('╔══════════════════════════════════════════════════════════╗');
    console.log(`║  TuBlox Server running on port ${PORT}                    ║`);
    console.log(`║  WebSocket path: /ws                                    ║`);
    console.log(`║  AntiCheat: ACTIVE                                      ║`);
    console.log(`║  Keep-Alive: ${SELF_URL ? 'ACTIVE' : 'DISABLED'}                                    ║`);
    console.log('╚══════════════════════════════════════════════════════════╝');
});