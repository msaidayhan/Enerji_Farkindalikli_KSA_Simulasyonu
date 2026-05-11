"""
Enerji Farkindalikli Multi-hop KSA Simulasyonu  v5
Kablosuz Sensor Aglari Dersi -- Mustafa Said Dayhan

v5 degisiklikleri:
 - Her senaryo kendi state'ini saklar (ScenarioState snapshot)
   Senaryo gecisinde mevcut state kaydedilir, hedef yuklenir
   Yeni harita olusturulunca tum state'ler sifirlanir
 - Uclu bitis kriteri:
     1) alive_count == 0                   (tam olum)
     2) teslim orani < %30 (son 20 paket)  (iletisim cokusu)
     3) alive_count < num_nodes * 0.30     (kritik dugum kaybi)
"""

import pygame
import math
import random
import heapq
import copy
from collections import defaultdict, deque

# ── RENKLER ──────────────────────────────────────────────────────────────────
BG           = (10,  14,  30)
PANEL_BG     = (18,  22,  45)
PANEL_DARK   = (12,  15,  32)
OVERLAY_COL  = (5,   8,   20)
WHITE        = (255, 255, 255)
GRAY         = (120, 130, 150)
DARK_GRAY    = (50,  55,  70)
ACCENT_BLUE  = (64,  130, 255)
ACCENT_CYAN  = (0,   200, 220)
ACCENT_GOLD  = (255, 190, 50)
GREEN        = (50,  210, 100)
GREEN_DIM    = (30,  100, 55)
YELLOW       = (240, 200, 40)
ORANGE       = (255, 140, 40)
RED          = (220, 60,  60)
RED_DIM      = (90,  28,  28)
DEAD_COLOR   = (45,  48,  60)
KILLED_COLOR = (180, 40,  140)
ISOLATED_COL = (255, 120, 0)
LOW_E_COL    = (180, 100, 20)
BS_COLOR     = (130, 80,  255)
EDGE_COLOR   = (40,  55,  90)
EDGE_ACTIVE  = (100, 170, 255)
EDGE_DEAD    = (28,  32,  50)
PKT_COLOR    = (255, 230, 80)
SC_COLORS    = [ACCENT_BLUE, ACCENT_GOLD, GREEN]

# ── EKRAN / LAYOUT ───────────────────────────────────────────────────────────
W, H      = 1280, 760
TOPO_X    = 20
TOPO_Y    = 80
TOPO_W    = 730
TOPO_H    = 640
PANEL_X   = 765
PANEL_W   = W - PANEL_X - 12

# ── SİMÜLASYON SABİTLERİ ────────────────────────────────────────────────────
BS_ID            = 0
INIT_ENERGY      = 1000.0
TX_COST          = 12.0
ACTIVE_COST      = 3.0
SLEEP_COST       = 0.3
RELAY_THRESHOLD  = 0.20
STEP_DELAY       = 120
DELIVERY_WINDOW  = 20
DELIVERY_MIN     = 0.30
ALIVE_MIN_RATIO  = 0.30   # canli dugum bu oranin altina duserse biter
PARTITION_CHECK  = 10

SCENARIO_NAMES = ["Surekli Aktif (%100)", "Kismi Aktif (%30)", "Dusuk Aktif (%10)"]
DUTY_VALUES    = [1.00, 0.30, 0.10]


# ── TOPOLOJI ────────────────────────────────────────────────────────────────
def build_topology(num_nodes, connect_dist, seed):
    rng = random.Random(seed)
    cx, cy = TOPO_X + TOPO_W // 2, TOPO_Y + TOPO_H // 2
    positions = [(cx, cy)]

    remaining = num_nodes - 1
    radii = [130, 255, 375]
    rings = []
    for ri, radius in enumerate(radii):
        cnt = min(remaining, [6, 8, remaining][ri])
        rings.append((cnt, radius))
        remaining -= cnt
        if remaining <= 0:
            break

    nid = 1
    for count, radius in rings:
        for i in range(count):
            if nid >= num_nodes:
                break
            angle = 2 * math.pi * i / count + rng.uniform(-0.25, 0.25)
            x = cx + int(radius * math.cos(angle)) + rng.randint(-20, 20)
            y = cy + int(radius * math.sin(angle)) + rng.randint(-20, 20)
            x = max(TOPO_X + 28, min(TOPO_X + TOPO_W - 28, x))
            y = max(TOPO_Y + 28, min(TOPO_Y + TOPO_H - 28, y))
            positions.append((x, y))
            nid += 1

    edges = set()
    for i in range(num_nodes):
        dists = sorted(
            [(math.hypot(positions[i][0]-positions[j][0],
                         positions[i][1]-positions[j][1]), j)
             for j in range(num_nodes) if j != i])
        connected = 0
        for d, j in dists:
            if d < connect_dist:
                edges.add((min(i, j), max(i, j)))
                connected += 1
            if connected >= 4:
                break
    return positions, list(edges)


# ── DÜĞÜM ────────────────────────────────────────────────────────────────────
class Node:
    def __init__(self, nid, x, y, init_e=INIT_ENERGY):
        self.id     = nid
        self.x      = x
        self.y      = y
        self.init_e = init_e
        self.reset()

    def reset(self):
        self.energy       = self.init_e
        self.alive        = True
        self.state        = "idle"
        self.killed       = False
        self.isolated     = False
        self.can_relay    = True
        self.energy_hist  = deque(maxlen=80)
        self.tx_count     = 0
        self.rx_count     = 0
        self.state_counts = {"idle":0,"active":0,"sleep":0,"tx":0}

    def color(self):
        if not self.alive:
            return KILLED_COLOR if self.killed else DEAD_COLOR
        if not self.can_relay:
            return LOW_E_COL
        ratio = self.energy / self.init_e
        if ratio > 0.6:
            r = int(50  + (1-ratio)*240)
            g = int(210 - (1-ratio)*70)
            b = int(100 - (1-ratio)*80)
            return (max(0,min(255,r)), max(0,min(255,g)), max(0,min(255,b)))
        elif ratio > 0.3:
            t = (ratio-0.3)/0.3
            return (240, int(140+t*60), 40)
        else:
            t = ratio/0.3
            return (220, int(60*t), int(60*t))

    def consume(self, duty_cycle):
        if not self.alive:
            return
        if self.state == "tx":
            self.energy -= TX_COST
            self.state_counts["tx"] += 1
            self.state = "idle"
        elif random.random() < duty_cycle:
            self.state = "active"
            self.energy -= ACTIVE_COST
            self.state_counts["active"] += 1
        else:
            self.state = "sleep"
            self.energy -= SLEEP_COST
            self.state_counts["sleep"] += 1
        self.energy_hist.append(max(0, self.energy))
        self.can_relay = (self.energy / self.init_e) >= RELAY_THRESHOLD
        if self.energy <= 0:
            self.energy = 0
            self.alive  = False
            self.state  = "dead"

    def snapshot(self):
        return {
            "energy":       self.energy,
            "alive":        self.alive,
            "state":        self.state,
            "killed":       self.killed,
            "isolated":     self.isolated,
            "can_relay":    self.can_relay,
            "energy_hist":  deque(self.energy_hist, maxlen=80),
            "tx_count":     self.tx_count,
            "rx_count":     self.rx_count,
            "state_counts": dict(self.state_counts),
        }

    def load_snapshot(self, snap):
        self.energy       = snap["energy"]
        self.alive        = snap["alive"]
        self.state        = snap["state"]
        self.killed       = snap["killed"]
        self.isolated     = snap["isolated"]
        self.can_relay    = snap["can_relay"]
        self.energy_hist  = deque(snap["energy_hist"], maxlen=80)
        self.tx_count     = snap["tx_count"]
        self.rx_count     = snap["rx_count"]
        self.state_counts = dict(snap["state_counts"])


# ── SENARYO STATE ─────────────────────────────────────────────────────────────
class ScenarioState:
    """Bir senaryonun tam anlık goruntusunu saklar."""
    def __init__(self):
        self.node_snaps   = None   # list of node.snapshot()
        self.step         = 0
        self.fnd          = None
        self.delivered    = 0
        self.lost         = 0
        self.pkt_window   = deque()
        self.active_path  = []
        self.active_path_t= 0
        self.started      = False  # hic baslatildi mi
        self.finished     = False
        self.result       = None   # sonuc dict

    def save(self, nodes, step, fnd, delivered, lost, pkt_window,
             active_path, active_path_t):
        self.node_snaps    = [n.snapshot() for n in nodes]
        self.step          = step
        self.fnd           = fnd
        self.delivered     = delivered
        self.lost          = lost
        self.pkt_window    = deque(pkt_window)
        self.active_path   = list(active_path)
        self.active_path_t = active_path_t
        self.started       = True

    def load(self, nodes):
        if self.node_snaps is None:
            for n in nodes: n.reset()
        else:
            for n, snap in zip(nodes, self.node_snaps):
                n.load_snapshot(snap)


# ── PAKET ────────────────────────────────────────────────────────────────────
class Packet:
    def __init__(self, path, nodes):
        self.path  = path
        self.nodes = nodes
        self.seg   = 0
        self.t     = 0.0
        self.speed = 0.06
        self.done  = False
        self.x     = float(nodes[path[0]].x)
        self.y     = float(nodes[path[0]].y)

    def update(self):
        if self.done or len(self.path) < 2:
            self.done = True; return
        if self.seg >= len(self.path)-1:
            self.done = True; return
        self.t += self.speed
        if self.t >= 1.0:
            self.t = 0.0; self.seg += 1
            if self.seg >= len(self.path)-1:
                self.done = True; return
        a, b = self.path[self.seg], self.path[self.seg+1]
        self.x = self.nodes[a].x + (self.nodes[b].x-self.nodes[a].x)*self.t
        self.y = self.nodes[a].y + (self.nodes[b].y-self.nodes[a].y)*self.t

    def draw(self, surf):
        if not self.done:
            ix, iy = int(self.x), int(self.y)
            pygame.draw.circle(surf, PKT_COLOR, (ix, iy), 7)
            pygame.draw.circle(surf, WHITE,     (ix, iy), 7, 1)


# ── DİJKSTRA ─────────────────────────────────────────────────────────────────
def energy_dijkstra(nodes, edges, src, dst):
    adj = defaultdict(list)
    for (a, b) in edges:
        na, nb = nodes[a], nodes[b]
        if not (na.alive and nb.alive):
            continue
        d = math.hypot(na.x-nb.x, na.y-nb.y)
        if nb.can_relay or b == dst:
            adj[a].append((d / (nb.energy**2 + 1), b))
        if na.can_relay or a == dst:
            adj[b].append((d / (na.energy**2 + 1), a))

    dist = defaultdict(lambda: float('inf'))
    prev = {}
    dist[src] = 0.0
    pq = [(0.0, src)]
    while pq:
        d, u = heapq.heappop(pq)
        if d > dist[u]: continue
        for cost, v in adj[u]:
            nd = dist[u]+cost
            if nd < dist[v]:
                dist[v] = nd; prev[v] = u
                heapq.heappush(pq, (nd, v))

    path, cur = [], dst
    while cur in prev:
        path.append(cur); cur = prev[cur]
    path.append(src); path.reverse()
    return path if len(path) >= 2 and path[0]==src and path[-1]==dst else []


# ── AG BOLUNME ───────────────────────────────────────────────────────────────
def check_partition(nodes, edges):
    if not nodes[BS_ID].alive:
        for n in nodes: n.isolated = n.alive
        return
    adj = defaultdict(set)
    for (a,b) in edges:
        if nodes[a].alive and nodes[b].alive:
            adj[a].add(b); adj[b].add(a)
    visited = {BS_ID}
    q = deque([BS_ID])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if v not in visited:
                visited.add(v); q.append(v)
    for n in nodes:
        n.isolated = n.alive and (n.id not in visited)


# ── GRAFİK ───────────────────────────────────────────────────────────────────
class EnergyGraph:
    def __init__(self):
        self.data   = [[] for _ in range(3)]
        self.frozen = [False]*3
        self.max_e  = 1.0

    def reset(self, num_nodes, init_e):
        self.data   = [[] for _ in range(3)]
        self.frozen = [False]*3
        self.max_e  = init_e * num_nodes

    def push(self, sc_idx, step, val):
        if not self.frozen[sc_idx]:
            self.data[sc_idx].append((step, val))

    def freeze(self, sc_idx):
        self.frozen[sc_idx] = True

    def draw(self, surf, font_xs, active_idx, x, y, w, h):
        pygame.draw.rect(surf, PANEL_DARK, (x, y, w, h), border_radius=8)
        pygame.draw.rect(surf, DARK_GRAY,  (x, y, w, h), 1, border_radius=8)

        lbl = font_xs.render("Enerji Tukenim Grafigi", True, WHITE)
        surf.blit(lbl, (x+7, y+4))

        # Lejant: basliktan sonra ayri satirda, esit aralikli
        sc_shorts = ["Surekli Aktif", "Kismi Aktif", "Dusuk Aktif"]
        leg_y = y + 18
        for i, (col, sh) in enumerate(zip(SC_COLORS, sc_shorts)):
            lx = x + 7 + i * (w // 3)
            pygame.draw.line(surf, col, (lx, leg_y+5), (lx+12, leg_y+5), 2)
            t = font_xs.render(sh, True, col)
            surf.blit(t, (lx+14, leg_y))

        # Grafik alani baslik+lejant altinda basliyor
        gx = x+7; gy = y+34; gw = w-14; gh = h-42
        for gi in range(1, 4):
            ly = gy + int(gi/4*gh)
            pygame.draw.line(surf, (30,36,58), (gx,ly), (gx+gw,ly), 1)

        max_step = max((d[-1][0] if d else 0) for d in self.data) or 1

        for i, (col, pts) in enumerate(zip(SC_COLORS, self.data)):
            if len(pts) < 2: continue
            is_active = (i==active_idx and not self.frozen[i])
            lw    = 2 if is_active else 1
            alpha = 255 if (is_active or self.frozen[i]) else 55
            draw_pts = []
            for step, val in pts:
                sx = gx + int(step/max_step*gw)
                sy = gy + gh - int(val/self.max_e*gh)
                draw_pts.append((sx, max(gy, min(gy+gh, sy))))
            for k in range(len(draw_pts)-1):
                c = tuple(int(ch*alpha/255) for ch in col)
                pygame.draw.line(surf, c, draw_pts[k], draw_pts[k+1], lw)
            if self.frozen[i] and draw_pts:
                pygame.draw.circle(surf, col, draw_pts[-1], 4)


# ── ÇIZIM YARDIMCILARI ───────────────────────────────────────────────────────
def draw_rrect(surf, color, rect, r=8, border=0, bcol=None):
    pygame.draw.rect(surf, color, rect, border_radius=r)
    if border:
        pygame.draw.rect(surf, bcol or DARK_GRAY, rect, border, border_radius=r)

def draw_play_icon(surf, x, y, size, col):
    pygame.draw.polygon(surf, col, [(x,y-size//2),(x,y+size//2),(x+size,y)])

def draw_pause_icon(surf, x, y, size, col):
    bw = max(2, size//3)
    pygame.draw.rect(surf, col, (x,         y-size//2, bw, size))
    pygame.draw.rect(surf, col, (x+size-bw, y-size//2, bw, size))

def draw_reset_icon(surf, x, y, size, col):
    pygame.draw.arc(surf, col, (x-size//2, y-size//2, size, size),
                    math.radians(40), math.radians(320), 2)
    pygame.draw.polygon(surf, col,
        [(x+size//2,y-2),(x+size//2+5,y+3),(x+size//2-1,y+5)])

def draw_button(surf, font, text, rect, hovered=False, active=False,
                icon=None, disabled=False):
    if disabled:
        bg, bc = (22,26,42), (38,42,58)
    else:
        bg = ACCENT_BLUE if active else ((55,70,110) if hovered else (35,42,70))
        bc = ACCENT_BLUE if active else DARK_GRAY
    draw_rrect(surf, bg, rect, r=7)
    pygame.draw.rect(surf, bc, rect, 1, border_radius=7)

    tw  = font.size(text)[0]
    cx  = rect[0]+rect[2]//2
    cy  = rect[1]+rect[3]//2
    iw  = 18 if icon else 0
    col = GRAY if disabled else WHITE
    ix  = cx - tw//2 - iw

    if icon=="play":    draw_play_icon (surf, ix, cy, 10, col)
    elif icon=="pause": draw_pause_icon(surf, ix, cy, 10, col)
    elif icon=="reset": draw_reset_icon(surf, ix+6, cy, 12, col)

    t = font.render(text, True, col)
    surf.blit(t, (cx - tw//2 + (iw//2 if icon else 0), cy-t.get_height()//2))


# ── PARAMETRE PANELİ ─────────────────────────────────────────────────────────
class ParamPanel:
    def __init__(self, fonts):
        self.fonts       = fonts
        self.visible     = False
        self.num_nodes   = 18
        self.conn_dist   = 220
        self.init_e      = 1000
        self.random_seed = True
        self.seed_val    = 42
        self.dragging    = None
        PW, PH           = 460, 310
        self.rect        = pygame.Rect((W-PW)//2, (H-PH)//2, PW, PH)
        self._sliders    = {}
        self._cb_rect    = None
        self._btn_apply  = None
        self._btn_cancel = None

    def draw(self, surf):
        if not self.visible: return
        font_l, font_m, font_s, _ = self.fonts
        ov = pygame.Surface((W,H), pygame.SRCALPHA)
        ov.fill((0,0,0,160)); surf.blit(ov,(0,0))
        draw_rrect(surf, PANEL_BG, self.rect, r=12)
        pygame.draw.rect(surf, ACCENT_BLUE, self.rect, 2, border_radius=12)
        rx, ry = self.rect.x, self.rect.y

        t = font_l.render("Yeni Topoloji Olustur", True, ACCENT_CYAN)
        surf.blit(t, (rx+20, ry+16))

        params = [
            ("Dugum Sayisi",       self.num_nodes, 8,   30,   "num_nodes", ry+62),
            ("Baglanti Menzili",   self.conn_dist, 120, 380,  "conn_dist", ry+122),
            ("Baslangic Enerjisi", self.init_e,    200, 2000, "init_e",    ry+182),
        ]
        self._sliders = {}
        for label, val, mn, mx, key, py in params:
            t = font_s.render(f"{label}: {val}", True, WHITE)
            surf.blit(t, (rx+20, py))
            bx=rx+20; by=py+22; bw=self.rect.w-40; bh=8
            pygame.draw.rect(surf, DARK_GRAY,  (bx,by,bw,bh), border_radius=4)
            ratio = (val-mn)/(mx-mn)
            pygame.draw.rect(surf, ACCENT_BLUE,(bx,by,int(ratio*bw),bh), border_radius=4)
            hx = bx+int(ratio*bw)
            pygame.draw.circle(surf, WHITE,       (hx,by+bh//2), 9)
            pygame.draw.circle(surf, ACCENT_BLUE, (hx,by+bh//2), 7)
            self._sliders[key] = (bx,by,bw,bh,mn,mx)

        sy = ry+242
        t = font_s.render("Rastgele Harita:", True, WHITE)
        surf.blit(t, (rx+20,sy))
        cb = pygame.Rect(rx+172, sy, 18, 18)
        pygame.draw.rect(surf, ACCENT_BLUE if self.random_seed else DARK_GRAY, cb, border_radius=4)
        if self.random_seed:
            t2 = font_s.render("v", True, WHITE); surf.blit(t2,(cb.x+3,cb.y+1))
        pygame.draw.rect(surf, WHITE, cb, 1, border_radius=4)
        self._cb_rect = cb
        if not self.random_seed:
            t = font_s.render(f"Seed: {self.seed_val}", True, GRAY)
            surf.blit(t, (rx+202,sy))

        self._btn_apply  = pygame.Rect(rx+self.rect.w-200, ry+self.rect.h-52, 88, 36)
        self._btn_cancel = pygame.Rect(rx+self.rect.w-104, ry+self.rect.h-52, 88, 36)
        draw_rrect(surf, ACCENT_BLUE, self._btn_apply,  r=7)
        draw_rrect(surf, (55,42,70),  self._btn_cancel, r=7)
        pygame.draw.rect(surf, DARK_GRAY, self._btn_cancel, 1, border_radius=7)
        for btn, lbl in [(self._btn_apply,"Uygula"),(self._btn_cancel,"Iptal")]:
            t = font_m.render(lbl, True, WHITE)
            surf.blit(t,(btn.x+(btn.w-t.get_width())//2, btn.y+(btn.h-t.get_height())//2))

    def handle_event(self, ev):
        if not self.visible: return None
        if ev.type == pygame.MOUSEBUTTONDOWN and ev.button==1:
            if self._btn_apply  and self._btn_apply.collidepoint(ev.pos):  return "apply"
            if self._btn_cancel and self._btn_cancel.collidepoint(ev.pos): return "cancel"
            if self._cb_rect    and self._cb_rect.collidepoint(ev.pos):
                self.random_seed = not self.random_seed; return None
            for key,(bx,by,bw,bh,mn,mx) in self._sliders.items():
                if abs(ev.pos[1]-(by+bh//2))<14 and bx<=ev.pos[0]<=bx+bw:
                    self.dragging=key; self._upd(key,ev.pos[0])
        if ev.type==pygame.MOUSEBUTTONUP   and ev.button==1: self.dragging=None
        if ev.type==pygame.MOUSEMOTION     and self.dragging: self._upd(self.dragging,ev.pos[0])
        return None

    def _upd(self, key, mx):
        bx,by,bw,bh,mn,mxv = self._sliders[key]
        val = int(mn + max(0.0,min(1.0,(mx-bx)/bw))*(mxv-mn))
        if key=="num_nodes":  self.num_nodes=val
        elif key=="conn_dist":self.conn_dist=val
        elif key=="init_e":   self.init_e=val


# ── DETAY PANELİ ─────────────────────────────────────────────────────────────
class DetailPanel:
    def __init__(self): self.node=None; self.visible=False
    def show(self,n):   self.node=n; self.visible=True
    def hide(self):     self.node=None; self.visible=False

    def draw(self, surf, fonts, x, y, w):
        if not self.visible or not self.node: return
        _, font_m, font_s, font_xs = fonts
        n=self.node; ph=215
        draw_rrect(surf, PANEL_DARK, (x,y,w,ph), r=8)
        bc = ACCENT_CYAN if n.alive else (KILLED_COLOR if n.killed else RED)
        pygame.draw.rect(surf, bc, (x,y,w,ph), 1, border_radius=8)

        status = "CANLI" if n.alive else ("KILL" if n.killed else "OLU")
        sc = GREEN if n.alive else (KILLED_COLOR if n.killed else RED)
        surf.blit(font_m.render(f"Dugum {n.id}  [{status}]", True, sc), (x+10,y+8))

        bx=x+10; by=y+32; bw=w-20; bh=10
        ratio = n.energy/n.init_e
        pygame.draw.rect(surf, DARK_GRAY, (bx,by,bw,bh), border_radius=5)
        fc = GREEN if ratio>0.5 else (YELLOW if ratio>0.25 else RED)
        pygame.draw.rect(surf, fc, (bx,by,int(ratio*bw),bh), border_radius=5)
        surf.blit(font_xs.render(f"Enerji: {int(n.energy)}/{int(n.init_e)}", True, WHITE),(bx,by+13))
        if n.alive and not n.can_relay:
            surf.blit(font_xs.render("!! Relay Esigi Altinda", True, LOW_E_COL),(bx,by+26))

        stats=[("Gonderilen", str(n.tx_count)),("Yonlendirilen",str(n.rx_count)),
               ("Aktif Adim", str(n.state_counts.get("active",0))),
               ("Uyku Adim",  str(n.state_counts.get("sleep",0))),
               ("TX Adim",    str(n.state_counts.get("tx",0)))]
        sy=y+58
        for lbl,val in stats:
            surf.blit(font_xs.render(lbl+":",True,GRAY),(x+10,sy))
            t=font_xs.render(val,True,ACCENT_GOLD)
            surf.blit(t,(x+w-t.get_width()-10,sy)); sy+=18

        gh=46; gy2=y+ph-gh-8; gx2=x+8; gw2=w-16
        pygame.draw.rect(surf,(18,23,42),(gx2,gy2,gw2,gh),border_radius=4)
        hist=list(n.energy_hist)
        if len(hist)>1:
            pts=[(gx2+int(ki/(len(hist)-1)*gw2), gy2+gh-int(v/n.init_e*gh))
                 for ki,v in enumerate(hist)]
            for ki in range(len(pts)-1):
                pygame.draw.line(surf,ACCENT_CYAN,pts[ki],pts[ki+1],1)
        surf.blit(font_xs.render("Enerji Gecmisi",True,GRAY),(gx2+2,gy2-12))


# ── RAPOR ─────────────────────────────────────────────────────────────────────
class ReportScreen:
    def __init__(self): self.visible=False; self._close=None

    def draw(self, surf, fonts, results, graph, num_nodes, init_e):
        if not self.visible: return
        font_l, font_m, font_s, font_xs = fonts
        ov=pygame.Surface((W,H),pygame.SRCALPHA)
        ov.fill((*OVERLAY_COL,235)); surf.blit(ov,(0,0))
        RW,RH=860,600; rx=(W-RW)//2; ry=(H-RH)//2
        draw_rrect(surf,PANEL_BG,(rx,ry,RW,RH),r=14)
        pygame.draw.rect(surf,ACCENT_CYAN,(rx,ry,RW,RH),2,border_radius=14)

        t=font_l.render("Senaryo Karsilastirma Raporu",True,ACCENT_CYAN)
        surf.blit(t,(rx+(RW-t.get_width())//2,ry+14))
        t=font_s.render(
            f"Dugum Sayisi: {num_nodes}   Baslangic Enerjisi: {int(init_e)}/dugum",
            True, GRAY)
        surf.blit(t,(rx+16,ry+44))

        # Sutunlar: Senaryo | Ilk Dugum Olumu | Ag Omru | Verimlilik | Bitis Sebebi
        COL_X = [rx+16, rx+200, rx+340, rx+450, rx+580]
        HDRS  = ["Ilk Dugum Olumu", "Ag Omru", "Verimlilik", "Bitis Sebebi"]
        ty = ry+70
        surf.blit(font_s.render("Senaryo", True, GRAY), (COL_X[0]+8, ty))
        for hx, hdr in zip(COL_X[1:], HDRS):
            surf.blit(font_s.render(hdr, True, GRAY), (hx, ty))
        pygame.draw.line(surf,DARK_GRAY,(rx+10,ty+20),(rx+RW-10,ty+20),1)
        ty+=26

        def best_worst(key, higher_better=True):
            vals = {i: results[i][key] for i in results if key in results[i]}
            if not vals: return None, None
            best  = max(vals, key=lambda i:vals[i]) if higher_better else min(vals, key=lambda i:vals[i])
            worst = min(vals, key=lambda i:vals[i]) if higher_better else max(vals, key=lambda i:vals[i])
            return best, worst

        fnd_best,  fnd_worst  = best_worst("fnd",      higher_better=True)
        life_best, life_worst = best_worst("lifetime",  higher_better=True)
        delv_best, delv_worst = best_worst("delivered", higher_better=True)

        def cell_col(sc_idx, best_idx, worst_idx):
            if sc_idx==best_idx:  return GREEN
            if sc_idx==worst_idx: return RED
            return WHITE

        ROW_H = 32
        for i,(nm,sc_col) in enumerate(zip(SCENARIO_NAMES,SC_COLORS)):
            if i not in results: continue
            r2     = results[i]
            fnd    = r2.get("fnd",0)
            life   = r2.get("lifetime",0)
            delv   = r2.get("delivered",0)
            lost   = r2.get("lost",0)
            eff    = f"%{int(delv/(delv+lost)*100)}" if (delv+lost)>0 else "-"
            reason = r2.get("reason","?")

            bg_col = (22,28,48) if i%2==0 else (18,22,40)
            pygame.draw.rect(surf,bg_col,pygame.Rect(rx+10,ty-2,RW-20,ROW_H-4),border_radius=5)
            pygame.draw.rect(surf,sc_col,(rx+10,ty-2,4,ROW_H-4),border_radius=2)

            t=font_xs.render(nm,True,sc_col)
            surf.blit(t,(COL_X[0]+8, ty+8))

            vals_cols=[
                (str(fnd),  cell_col(i,fnd_best,fnd_worst)),
                (str(life), cell_col(i,life_best,life_worst)),
                (eff,       cell_col(i,delv_best,delv_worst)),
                (reason,    WHITE),
            ]
            for cx2,(val,col) in zip(COL_X[1:],vals_cols):
                if col==GREEN:
                    vr=pygame.Rect(cx2-3,ty,font_s.size(val)[0]+6,ROW_H-8)
                    pygame.draw.rect(surf,GREEN_DIM,vr,border_radius=4)
                elif col==RED and val not in ("-","?"):
                    vr=pygame.Rect(cx2-3,ty,font_s.size(val)[0]+6,ROW_H-8)
                    pygame.draw.rect(surf,RED_DIM,vr,border_radius=4)
                t=font_s.render(val,True,col)
                surf.blit(t,(cx2,ty+6))
            ty+=ROW_H

        pygame.draw.line(surf,DARK_GRAY,(rx+10,ty+8),(rx+RW-10,ty+8),1)
        gx2=rx+16; gy2=ty+36; gw2=RW-32; gh2=RH-(ty+36-ry)-52
        graph.draw(surf,font_xs,3,gx2,gy2,gw2,gh2)

        # Grafik lejanti - ustuste binmesin diye grafik altina al
        leg_y2 = gy2 - 20
        leg_items=[(GREEN,"En iyi"),(RED,"En kotu"),(WHITE,"Orta")]
        lx2 = gx2 + gw2 - 200   # sag tarafa yasla, baslik yazilariyla catismasin
        for col,lbl in leg_items:
            if col!=WHITE:
                sample=pygame.Rect(lx2,leg_y2,12,12)
                pygame.draw.rect(surf,GREEN_DIM if col==GREEN else RED_DIM,sample,border_radius=3)
            t=font_xs.render(lbl,True,col)
            surf.blit(t,(lx2+16, leg_y2))
            lx2+=t.get_width()+36

        self._close=pygame.Rect(rx+RW//2-52,ry+RH-46,104,34)
        draw_rrect(surf,ACCENT_BLUE,self._close,r=8)
        t=font_m.render("Kapat",True,WHITE)
        surf.blit(t,(self._close.x+(104-t.get_width())//2,
                     self._close.y+(34-t.get_height())//2))

    def handle_click(self,pos):
        if self.visible and self._close and self._close.collidepoint(pos):
            self.visible=False; return True
        return False


# ── SİMÜLASYON ───────────────────────────────────────────────────────────────
class Simulation:
    def __init__(self, num_nodes=18, conn_dist=220, init_e=1000, seed=42):
        global INIT_ENERGY
        INIT_ENERGY    = float(init_e)
        self.num_nodes = num_nodes
        self.conn_dist = conn_dist
        self.init_e    = float(init_e)
        self.seed      = seed

        pos, edges     = build_topology(num_nodes, conn_dist, seed)
        self.base_pos  = pos
        self.edges     = edges
        self.nodes     = [Node(i,pos[i][0],pos[i][1],self.init_e) for i in range(num_nodes)]

        # Her senaryo icin ayri state
        self.sc_states = [ScenarioState() for _ in range(3)]
        self.sc_idx    = 0
        self.graph     = EnergyGraph()
        self.graph.reset(num_nodes, self.init_e)

        # Aktif calisma degiskenleri
        self._init_active()

    def _init_active(self):
        """Aktif senaryo calisma degiskenlerini sifirla."""
        self.step          = 0
        self.running       = False
        self.fnd           = None
        self.fnd_flash     = 0
        self.packets       = []
        self.active_path   = []
        self.active_path_t = 0
        self.send_timer    = 0
        self.delivered     = 0
        self.lost          = 0
        self.pkt_window    = deque()

    def duty(self): return DUTY_VALUES[self.sc_idx]

    def alive_count(self):
        return sum(1 for n in self.nodes if n.alive and n.id!=BS_ID)

    def total_energy(self):
        return sum(n.energy for n in self.nodes if n.alive)

    def delivery_rate(self):
        if not self.pkt_window: return 1.0
        return sum(self.pkt_window) / len(self.pkt_window)

    def _record_attempt(self, success):
        self.pkt_window.append(success)
        if len(self.pkt_window) > DELIVERY_WINDOW:
            self.pkt_window.popleft()

    def _end_reason(self):
        if self.alive_count()==0:
            return "Tam Olum"
        if self.alive_count() < self.num_nodes * ALIVE_MIN_RATIO:
            return f"Kritik Dugum Kaybi (<%{int(ALIVE_MIN_RATIO*100)})"
        return f"Dusuk Teslim (<%{int(DELIVERY_MIN*100)})"

    def _should_end(self):
        ac = self.alive_count()
        if ac == 0:
            return True
        if ac < self.num_nodes * ALIVE_MIN_RATIO:
            return True
        if len(self.pkt_window)==DELIVERY_WINDOW and self.delivery_rate()<DELIVERY_MIN:
            return True
        return False

    def _save_current_to_state(self):
        """Aktif calisma durumunu sc_states[sc_idx]'e kaydet."""
        st = self.sc_states[self.sc_idx]
        st.save(self.nodes, self.step, self.fnd,
                self.delivered, self.lost, self.pkt_window,
                self.active_path, self.active_path_t)

    def _load_state(self, idx):
        """sc_states[idx]'i aktif degiskenlere yukle."""
        st = self.sc_states[idx]
        st.load(self.nodes)   # dugum state'lerini yukle
        self.step          = st.step
        self.fnd           = st.fnd
        self.delivered     = st.delivered
        self.lost          = st.lost
        self.pkt_window    = deque(st.pkt_window)
        self.active_path   = list(st.active_path)
        self.active_path_t = st.active_path_t
        self.fnd_flash     = 0
        self.running       = False
        self.packets       = []
        self.send_timer    = 0

    def switch_scenario(self, idx):
        if idx == self.sc_idx: return
        # Mevcut state'i kaydet
        self._save_current_to_state()
        self.sc_idx = idx
        # Hedef state'i yukle
        self._load_state(idx)

    def _finish_scenario(self):
        """Bitis kriterini karsilayan senaryoyu sonuclandir."""
        st = self.sc_states[self.sc_idx]
        if not st.finished:
            st.finished = True
            st.result   = {
                "fnd":       self.fnd or self.step,
                "lifetime":  self.step,
                "delivered": self.delivered,
                "lost":      self.lost,
                "reason":    self._end_reason(),
            }
            self.graph.freeze(self.sc_idx)
        self.running = False

    def results(self):
        return {i: self.sc_states[i].result
                for i in range(3) if self.sc_states[i].result is not None}

    def all_done(self):
        return all(self.sc_states[i].finished for i in range(3))

    def tick(self):
        self.step+=1

        for n in self.nodes:
            if n.id==BS_ID: continue
            n.consume(self.duty())
            if not n.alive and self.fnd is None:
                self.fnd=self.step; self.fnd_flash=90

        if self.step%PARTITION_CHECK==0:
            check_partition(self.nodes,self.edges)

        self.send_timer-=1
        if self.send_timer<=0:
            self.send_timer=max(3, 8-self.speed_mult*2)
            srcs=[n for n in self.nodes if n.alive and n.id!=BS_ID]
            if srcs:
                src =random.choice(srcs)
                path=energy_dijkstra(self.nodes,self.edges,src.id,BS_ID)
                if len(path)>1:
                    self.active_path=path; self.active_path_t=40
                    self.packets.append(Packet(path,self.nodes))
                    src.tx_count+=1
                    for pid in path[1:-1]:
                        if self.nodes[pid].alive:
                            self.nodes[pid].energy=max(0,self.nodes[pid].energy-TX_COST*0.5)
                            self.nodes[pid].state="tx"
                            self.nodes[pid].rx_count+=1
                    self.delivered+=1; self._record_attempt(True)
                else:
                    self.lost+=1; self._record_attempt(False)

        self.packets=[p for p in self.packets if not p.done]
        for p in self.packets: p.update()
        if self.active_path_t>0: self.active_path_t-=1
        if self.fnd_flash>0:     self.fnd_flash-=1

        self.graph.push(self.sc_idx, self.step, self.total_energy())
        self.sc_states[self.sc_idx].started = True

        if self._should_end() and not self.sc_states[self.sc_idx].finished:
            self._finish_scenario()

    def kill_node(self, nid):
        n=self.nodes[nid]
        if n.alive and nid!=BS_ID:
            n.alive=False; n.energy=0; n.state="dead"; n.killed=True
            if self.fnd is None: self.fnd=self.step; self.fnd_flash=90
            self.lost+=1; self._record_attempt(False)
            check_partition(self.nodes,self.edges)

    def node_at(self,mx,my,r=18):
        for n in self.nodes:
            if math.hypot(n.x-mx,n.y-my)<r: return n
        return None


# ── ANA DÖNGÜ ─────────────────────────────────────────────────────────────────
def main():
    pygame.init()
    screen=pygame.display.set_mode((W,H), pygame.SCALED|pygame.RESIZABLE)
    pygame.display.set_caption("KSA Enerji Simulasyonu -- Mustafa Said Dayhan")
    clock=pygame.time.Clock()

    try:
        font_l  = pygame.font.SysFont("Segoe UI",22,bold=True)
        font_m  = pygame.font.SysFont("Segoe UI",16)
        font_s  = pygame.font.SysFont("Segoe UI",13)
        font_xs = pygame.font.SysFont("Segoe UI",11)
    except:
        font_l  = pygame.font.SysFont(None,24,bold=True)
        font_m  = pygame.font.SysFont(None,18)
        font_s  = pygame.font.SysFont(None,14)
        font_xs = pygame.font.SysFont(None,12)
    fonts=(font_l,font_m,font_s,font_xs)

    sim         = Simulation()
    sim.speed_mult = 1
    param_panel = ParamPanel(fonts)
    detail      = DetailPanel()
    report      = ReportScreen()

    BTN_H=32; GAP=5; by=TOPO_Y; half=(PANEL_W-GAP)//2
    btns={
        "start":  pygame.Rect(PANEL_X,          by,               half,    BTN_H),
        "reset":  pygame.Rect(PANEL_X+half+GAP, by,               half,    BTN_H),
        "s0":     pygame.Rect(PANEL_X, by+1*(BTN_H+GAP),          PANEL_W, BTN_H),
        "s1":     pygame.Rect(PANEL_X, by+2*(BTN_H+GAP),          PANEL_W, BTN_H),
        "s2":     pygame.Rect(PANEL_X, by+3*(BTN_H+GAP),          PANEL_W, BTN_H),
        "slower": pygame.Rect(PANEL_X,          by+4*(BTN_H+GAP), half,    BTN_H),
        "faster": pygame.Rect(PANEL_X+half+GAP, by+4*(BTN_H+GAP), half,    BTN_H),
        "report": pygame.Rect(PANEL_X, by+5*(BTN_H+GAP)+2,        PANEL_W, BTN_H),
    }

    METRICS_Y = btns["report"].bottom+10
    METRICS_H = 6*29
    DETAIL_Y  = METRICS_Y
    GRAPH_Y   = METRICS_Y+METRICS_H+8
    GRAPH_H   = H-GRAPH_Y-12

    mouse_pos=(0,0); last_tick=pygame.time.get_ticks()

    while True:
        clock.tick(60)
        now=pygame.time.get_ticks()
        mouse_pos=pygame.mouse.get_pos()
        shift=pygame.key.get_mods()&pygame.KMOD_SHIFT

        for ev in pygame.event.get():
            if ev.type==pygame.QUIT: pygame.quit(); return

            if report.handle_click(ev.pos if ev.type==pygame.MOUSEBUTTONDOWN else (-1,-1)):
                continue

            res=param_panel.handle_event(ev)
            if res=="apply":
                seed=random.randint(0,9999) if param_panel.random_seed else param_panel.seed_val
                sim=Simulation(param_panel.num_nodes,param_panel.conn_dist,
                               param_panel.init_e,seed)
                sim.speed_mult=1
                detail.hide(); param_panel.visible=False; continue
            elif res=="cancel":
                param_panel.visible=False; continue
            if param_panel.visible: continue

            if ev.type==pygame.KEYDOWN:
                if ev.key==pygame.K_SPACE:    sim.running=not sim.running
                elif ev.key==pygame.K_r:      param_panel.visible=True
                elif ev.key==pygame.K_1:      sim.switch_scenario(0); detail.hide()
                elif ev.key==pygame.K_2:      sim.switch_scenario(1); detail.hide()
                elif ev.key==pygame.K_3:      sim.switch_scenario(2); detail.hide()
                elif ev.key==pygame.K_ESCAPE: detail.hide()

            if ev.type==pygame.MOUSEBUTTONDOWN and ev.button==1:
                p=ev.pos
                if btns["start"].collidepoint(p):
                    if not sim.sc_states[sim.sc_idx].finished:
                        sim.running=not sim.running
                elif btns["reset"].collidepoint(p): param_panel.visible=True
                elif btns["s0"].collidepoint(p):    sim.switch_scenario(0); detail.hide()
                elif btns["s1"].collidepoint(p):    sim.switch_scenario(1); detail.hide()
                elif btns["s2"].collidepoint(p):    sim.switch_scenario(2); detail.hide()
                elif btns["slower"].collidepoint(p):sim.speed_mult=max(1,sim.speed_mult-1)
                elif btns["faster"].collidepoint(p):sim.speed_mult=min(5,sim.speed_mult+1)
                elif btns["report"].collidepoint(p) and sim.all_done():
                    report.visible=True
                else:
                    node=sim.node_at(*p)
                    if node:
                        if shift and node.alive and node.id!=BS_ID:
                            sim.kill_node(node.id); detail.show(node)
                        else:
                            detail.hide() if (detail.visible and detail.node==node) \
                                          else detail.show(node)

        delay=STEP_DELAY//sim.speed_mult
        if sim.running and (now-last_tick)>=delay:
            last_tick=now; sim.tick()

        # ── ÇİZİM ────────────────────────────────────────────────────────────
        screen.fill(BG)

        t=font_l.render("Kablosuz Sensor Aglarinda Enerji Tuketimi ve Ag Omru Simulasyonu",True,ACCENT_CYAN)
        screen.blit(t,(TOPO_X,12))
        t=font_s.render(f"Adim: {sim.step}",True,ACCENT_GOLD)
        screen.blit(t,(TOPO_X+TOPO_W-100,12))

        draw_rrect(screen,PANEL_BG,(TOPO_X,TOPO_Y,TOPO_W,TOPO_H),r=12)
        pygame.draw.rect(screen,DARK_GRAY,(TOPO_X,TOPO_Y,TOPO_W,TOPO_H),1,border_radius=12)

        active_e=set()
        if sim.active_path_t>0 and len(sim.active_path)>1:
            for k in range(len(sim.active_path)-1):
                a,b=sim.active_path[k],sim.active_path[k+1]
                active_e.add((min(a,b),max(a,b)))

        for (a,b) in sim.edges:
            na,nb=sim.nodes[a],sim.nodes[b]
            act=(min(a,b),max(a,b)) in active_e
            both=na.alive and nb.alive
            col=EDGE_ACTIVE if act else (EDGE_COLOR if both else EDGE_DEAD)
            pygame.draw.line(screen,col,(na.x,na.y),(nb.x,nb.y),2 if act else 1)

        for pkt in sim.packets: pkt.draw(screen)

        for n in sim.nodes:
            if n.id==BS_ID:
                r=22
                pygame.draw.circle(screen,(80,50,180),(n.x,n.y),r)
                pygame.draw.circle(screen,BS_COLOR,(n.x,n.y),r,3)
                lbl=font_s.render("BS",True,WHITE)
                screen.blit(lbl,(n.x-lbl.get_width()//2,n.y-lbl.get_height()//2))
                ph=(now%1200)/1200; rr=int(r+8+ph*18); ra=int(160*(1-ph))
                s=pygame.Surface((rr*2+4,rr*2+4),pygame.SRCALPHA)
                pygame.draw.circle(s,(*BS_COLOR,ra),(rr+2,rr+2),rr,2)
                screen.blit(s,(n.x-rr-2,n.y-rr-2))
                continue

            col=n.color(); r=14

            if n.isolated:
                ph2=(now%800)/800; a2=int(180+75*math.sin(ph2*2*math.pi))
                s2=pygame.Surface(((r+8)*2,(r+8)*2),pygame.SRCALPHA)
                pygame.draw.circle(s2,(*ISOLATED_COL,a2),(r+8,r+8),r+8,2)
                screen.blit(s2,(n.x-r-8,n.y-r-8))

            if sim.fnd_flash>0 and not n.alive:
                fc=RED if (sim.fnd_flash//8)%2==0 else (255,80,80)
                pygame.draw.circle(screen,fc,(n.x,n.y),r+5,3)

            if n.alive:
                ratio=n.energy/n.init_e; angle=int(360*ratio)
                if angle>3:
                    pygame.draw.arc(screen,col,
                        pygame.Rect(n.x-r-4,n.y-r-4,(r+4)*2,(r+4)*2),
                        math.radians(90),math.radians(90+angle),3)
            if n.alive and not n.can_relay:
                pygame.draw.circle(screen,LOW_E_COL,(n.x,n.y),r+6,1)

            pygame.draw.circle(screen,col,(n.x,n.y),r)
            if n.killed:
                pygame.draw.line(screen,KILLED_COLOR,(n.x-7,n.y-7),(n.x+7,n.y+7),2)
                pygame.draw.line(screen,KILLED_COLOR,(n.x+7,n.y-7),(n.x-7,n.y+7),2)
            pygame.draw.circle(screen,WHITE if n.alive else DARK_GRAY,(n.x,n.y),r,1)

            if detail.visible and detail.node==n:
                pygame.draw.circle(screen,ACCENT_CYAN,(n.x,n.y),r+5,2)
            if n.alive:
                sc_map={"idle":GRAY,"active":GREEN,"sleep":ACCENT_BLUE,"tx":PKT_COLOR}
                pygame.draw.circle(screen,sc_map.get(n.state,GRAY),(n.x+r-3,n.y-r+3),4)
            id_t=font_xs.render(str(n.id),True,WHITE if n.alive else DARK_GRAY)
            screen.blit(id_t,(n.x-id_t.get_width()//2,n.y-id_t.get_height()//2))

        # Lejant
        leg_y=TOPO_Y+TOPO_H+4
        legend=[("Yuksek Enerji",GREEN),("Orta Enerji",YELLOW),("Dusuk Enerji",ORANGE),("Kritik Enerji",RED),
                ("Zayif Dugum",LOW_E_COL),("Olu",DEAD_COLOR),("Kapatildi",KILLED_COLOR),("Izole",ISOLATED_COL)]
        lx=TOPO_X
        for txt,col in legend:
            pygame.draw.circle(screen,col,(lx+5,leg_y+6),5)
            t_=font_xs.render(txt,True,GRAY); screen.blit(t_,(lx+13,leg_y))
            lx+=t_.get_width()+22
        hint=font_xs.render(
            "SPACE:Baslat/Dur  R:Yeni Harita  1/2/3:Senaryo  Shift+Tikla:Dugumu Kapat  ESC:Kapat",
            True,DARK_GRAY)
        screen.blit(hint,(TOPO_X,H-14))

        # ── SAG PANEL ────────────────────────────────────────────────────────
        sc_finished = sim.sc_states[sim.sc_idx].finished
        if sim.running:
            draw_button(screen,font_m,"Durdur",btns["start"],
                hovered=btns["start"].collidepoint(mouse_pos),active=True,icon="pause")
        else:
            draw_button(screen,font_m,"Baslat",btns["start"],
                hovered=btns["start"].collidepoint(mouse_pos),
                icon="play", disabled=sc_finished)

        draw_button(screen,font_m,"Yeni Harita",btns["reset"],
            hovered=btns["reset"].collidepoint(mouse_pos),icon="reset")

        for i,(lbl,key,col) in enumerate(zip(SCENARIO_NAMES,["s0","s1","s2"],SC_COLORS)):
            is_act=(sim.sc_idx==i)
            draw_button(screen,font_m,lbl,btns[key],
                hovered=btns[key].collidepoint(mouse_pos),active=is_act)
            r_=btns[key]
            pygame.draw.rect(screen,col,(r_.x,r_.y+4,3,r_.height-8),border_radius=2)
            st=sim.sc_states[i]
            if st.finished:
                done_t=font_xs.render("TAMAM",True,GREEN)
                screen.blit(done_t,(r_.right-done_t.get_width()-8,
                                    r_.top+(r_.height-done_t.get_height())//2))
            elif st.started and not is_act:
                pause_t=font_xs.render("DEVAM",True,ACCENT_GOLD)
                screen.blit(pause_t,(r_.right-pause_t.get_width()-8,
                                     r_.top+(r_.height-pause_t.get_height())//2))

        draw_button(screen,font_m,"< Yavas",btns["slower"],
            hovered=btns["slower"].collidepoint(mouse_pos))
        draw_button(screen,font_m,"Hizli >",btns["faster"],
            hovered=btns["faster"].collidepoint(mouse_pos))
        spd=font_xs.render(f"Hiz: x{sim.speed_mult}",True,ACCENT_GOLD)
        screen.blit(spd,(PANEL_X+PANEL_W//2-spd.get_width()//2,btns["faster"].bottom+3))

        all_done=sim.all_done()
        draw_button(screen,font_m,"Raporu Goster",btns["report"],
            hovered=btns["report"].collidepoint(mouse_pos) and all_done,
            active=all_done,disabled=not all_done)

        # Metrikler / detay karti
        if detail.visible and detail.node:
            detail.draw(screen,fonts,PANEL_X,DETAIL_Y,PANEL_W)
        else:
            dr=sim.delivery_rate()
            dr_col=GREEN if dr>0.6 else (YELLOW if dr>0.3 else RED)
            dr_str=f"%{int(dr*100)}  ({sim.delivered}/{sim.delivered+sim.lost})"
            metrics=[
                ("Senaryo",      SCENARIO_NAMES[sim.sc_idx]),
                ("Adim",         str(sim.step)),
                ("Canli Dugum",  f"{sim.alive_count()} / {sim.num_nodes-1}"),
                ("Kalan Enerji", f"{int(sim.total_energy())}"),
                ("Teslim Orani", dr_str),
                ("Izole Dugum",  str(sum(1 for n in sim.nodes if n.isolated))),
            ]
            iy=METRICS_Y
            for label,val in metrics:
                draw_rrect(screen,PANEL_DARK,(PANEL_X,iy,PANEL_W,26),r=6)
                lt=font_s.render(label+":",True,GRAY)
                vc=WHITE
                if label=="Adim":          vc=ACCENT_GOLD
                elif label=="Kalan Enerji":vc=ACCENT_GOLD
                elif label=="Teslim Orani":vc=dr_col
                vt=font_s.render(val,True,vc)
                screen.blit(lt,(PANEL_X+8,iy+5))
                screen.blit(vt,(PANEL_X+PANEL_W-vt.get_width()-8,iy+5))
                iy+=29

        sim.graph.draw(screen,font_xs,sim.sc_idx,PANEL_X,GRAPH_Y,PANEL_W,GRAPH_H)

        if sim.fnd_flash>0:
            al=int(210*sim.fnd_flash/90)
            fl=pygame.Surface((TOPO_W,38),pygame.SRCALPHA)
            fl.fill((200,40,40,al)); screen.blit(fl,(TOPO_X,TOPO_Y))
            msg=font_l.render(f"UYARI: Ilk Dugum Olumu! (Adim {sim.fnd})",True,WHITE)
            screen.blit(msg,(TOPO_X+(TOPO_W-msg.get_width())//2,TOPO_Y+8))

        param_panel.draw(screen)
        report.draw(screen,fonts,sim.results(),sim.graph,sim.num_nodes,sim.init_e)

        pygame.display.flip()


if __name__=="__main__":
    main()
