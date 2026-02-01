# encoding: utf-8
###########################################################################################################
#
# Ballpoint pen Tool Plugin — v1.0 (with Visual Clamping Feedback and Full UI)
#
###########################################################################################################
from __future__ import division, print_function, unicode_literals
import objc, os, math
from GlyphsApp import Glyphs, GSPath, GSNode, GSOFFCURVE, GSCURVE, GSLINE, UPDATEINTERFACE
from GlyphsApp.plugins import SelectTool, PalettePlugin
from AppKit import NSImage, NSColor, NSBezierPath, NSPoint
# ----------------------------------------------------------
# Constantes globales
# ----------------------------------------------------------
DEFAULT_SIMPLIFY_EPSILON = 2.0
DEFAULT_STROKE_WIDTH = 20.0
MIN_DISTANCE = 4.0
MIN_SEGMENT_LENGTH = 5.0 # Seuil pour forcer une ligne droite aux extrémités
PINCH_FACTOR = 0.25      # 25% de la longueur du segment d'ancrage
# ----------------------------------------------------------
# Fonctions utilitaires
# ----------------------------------------------------------
def distance(p1, p2):
    return math.hypot(p2.x - p1.x, p2.y - p1.y)
def distance_point_segment(p, a, b):
    x, y = p.x, p.y
    x1, y1 = a.x, a.y
    x2, y2 = b.x, b.y
    dx = x2 - x1
    dy = y2 - y1
    if dx == 0 and dy == 0:
        return math.hypot(x - x1, y - y1)
    t = ((x - x1) * dx + (y - y1) * dy) / (dx * dx + dy * dy)
    t = max(0.0, min(1.0, t))
    projx = x1 + t * dx
    projy = y1 + t * dy
    return math.hypot(x - projx, y - projy)
def rdp_simplify(points, epsilon):
    if len(points) < 3:
        return points[:]
    dmax = 0.0
    index = 0
    a = points[0]
    b = points[-1]
    for i in range(1, len(points) - 1):
        d = distance_point_segment(points[i], a, b)
        if d > dmax:
            index = i
            dmax = d
    if dmax > epsilon:
        left = rdp_simplify(points[: index + 1], epsilon)
        right = rdp_simplify(points[index:], epsilon)
        return left[:-1] + right
    else:
        return [points[0], points[-1]]

def simplify_ends(points, num_points_to_process=5, epsilon_ends=1.0):
    if len(points) < 2: return points[:]
    if len(points) <= num_points_to_process * 2: return rdp_simplify(points, epsilon_ends)

    start_segment = points[:num_points_to_process]
    simplified_start = rdp_simplify(start_segment, epsilon_ends)
    
    end_segment = points[len(points) - num_points_to_process:]
    simplified_end = rdp_simplify(end_segment, epsilon_ends)
    
    new_points = []
    for p in simplified_start:
        if not new_points or distance(p, new_points[-1]) > 0.1: new_points.append(p)
            
    junction_start_index = len(simplified_start) - 1 if len(simplified_start) > 0 else 0
    junction_end_index = len(points) - len(simplified_end) if len(simplified_end) > 0 else len(points)
    
    for i in range(junction_start_index, junction_end_index):
        p = points[i]
        if not new_points or distance(p, new_points[-1]) > 0.1: new_points.append(p)

    for p in simplified_end:
        if not new_points or distance(p, new_points[-1]) > 0.1: new_points.append(p)
            
    return new_points

def cleanup_endpoints(points, min_distance=5.0):
    if len(points) < 3: return points[:]
    start_point = points[0]
    end_point = points[-1]
    cleaned_points = [start_point]
    for i in range(1, len(points) - 1):
        p = points[i]
        if not (distance(p, start_point) < min_distance or distance(p, end_point) < min_distance):
            cleaned_points.append(p)
            
    if distance(cleaned_points[-1], end_point) > 1e-6: cleaned_points.append(end_point)
    return cleaned_points

def ns_add(a, b): return NSPoint(a.x + b.x, a.y + b.y)
def ns_sub(a, b): return NSPoint(a.x - b.x, a.y - b.y)
def ns_mul(a, s): return NSPoint(a.x * s, a.y * s)
def ns_div(a, s): return NSPoint(a.x / s, a.y / s)

def ns_limit_length(vector, max_length):
    length = distance(NSPoint(0, 0), vector)
    if length > max_length and length > 1e-6:
        return ns_mul(vector, max_length / length)
    return vector

def make_tangent_symmetric(p_anchor, p_control_out):
    return ns_sub(ns_mul(p_anchor, 2.0), p_control_out)

def b_spline_to_bezier(points):
    n = len(points)
    if n < 2: return []
    if n == 2:
        p0, p1 = points
        c1 = ns_add(p0, ns_mul(ns_sub(p1, p0), 1/3))
        c2 = ns_add(p0, ns_mul(ns_sub(p1, p0), 2/3))
        return [(p0, c1, c2, p1)]
    padded = [points[0], points[0]] + points[:] + [points[-1], points[-1]]
    beziers = []
    for i in range(len(padded) - 3):
        P0, P1, P2, P3 = padded[i], padded[i + 1], padded[i + 2], padded[i + 3]
        Q0 = ns_div(ns_add(ns_add(P0, ns_mul(P1, 4.0)), P2), 6.0)
        Q1 = ns_div(ns_add(ns_mul(P1, 4.0), ns_mul(P2, 2.0)), 6.0)
        Q2 = ns_div(ns_add(ns_mul(P1, 2.0), ns_mul(P2, 4.0)), 6.0)
        Q3 = ns_div(ns_add(ns_add(P1, ns_mul(P2, 4.0)), P3), 6.0)
        beziers.append((Q0, Q1, Q2, Q3))
    return [seg for seg in beziers if abs(seg[0].x - seg[3].x) > 1e-6 or abs(seg[0].y - seg[3].y) > 1e-6]

def trim_ends(points, trim_length=2.0):
    if len(points) < 3:
        return points[:]
    def trim_segment(points, trim_length, from_start=True):
        d = 0
        if from_start:
            for i in range(len(points) - 1):
                seg_len = distance(points[i], points[i + 1])
                if d + seg_len >= trim_length:
                    ratio = (trim_length - d) / seg_len
                    new_p = NSPoint(points[i].x + (points[i + 1].x - points[i].x) * ratio, points[i].y + (points[i + 1].y - points[i].y) * ratio)
                    return [new_p] + points[i + 1:]
                d += seg_len
            return points
        else:
            for i in range(len(points) - 1, 0, -1):
                seg_len = distance(points[i], points[i - 1])
                if d + seg_len >= trim_length:
                    ratio = (trim_length - d) / seg_len
                    new_p = NSPoint(points[i].x + (points[i - 1].x - points[i].x) * ratio, points[i].y + (points[i - 1].y - points[i].y) * ratio)
                    return points[:i] + [new_p]
                d += seg_len
            return points
    trim = trim_length * 2.0 
    trimmed = trim_segment(points, trim, from_start=True)
    trimmed = trim_segment(trimmed, trim, from_start=False)
    if distance(trimmed[0], trimmed[1]) < 0.1 and len(trimmed) > 2:
        trimmed = trimmed[1:]
    if distance(trimmed[-1], trimmed[-2]) < 0.1 and len(trimmed) > 2:
        trimmed = trimmed[:-1]
    return trimmed


# FONCTION CLAMPING GÉNÉRIQUE (utilisée par mouseUp et background)
def apply_clamping(beziers):
    if not beziers:
        return beziers, None, None
    
    # Le dictionnaire sera retourné pour le repère visuel
    clamped_points = {'start': None, 'end': None}
    
    # --- Traitement du segment de début (p0, c1, c2, p1) ---
    p0_first, c1_first, c2_first, p1_first = beziers[0]
    
    vec_p0_p1 = ns_sub(p1_first, p0_first)
    len_p0_p1 = distance(NSPoint(0, 0), vec_p0_p1)
    
    if len_p0_p1 < MIN_SEGMENT_LENGTH:
        # Segment trop court: forcer C1 = P0 pour faire une ligne droite
        if distance(c1_first, p0_first) > 0.1:
            c1_first = p0_first
            clamped_points['start'] = p0_first
    elif len_p0_p1 > 1e-6:
        max_c1_len = len_p0_p1 * PINCH_FACTOR
        vec_p0_c1 = ns_sub(c1_first, p0_first)
        
        unit_vec_p0_p1 = ns_div(vec_p0_p1, len_p0_p1)
        dot_product = vec_p0_c1.x * unit_vec_p0_p1.x + vec_p0_c1.y * unit_vec_p0_p1.y
        
        if dot_product < 0:
            c1_first = ns_add(p0_first, ns_mul(unit_vec_p0_p1, max_c1_len))
            clamped_points['start'] = c1_first
        else:
            vec_p0_c1_limited = ns_limit_length(vec_p0_c1, max_c1_len)
            c1_first_new = ns_add(p0_first, vec_p0_c1_limited)
            if distance(c1_first_new, c1_first) > 0.1:
                c1_first = c1_first_new
                clamped_points['start'] = c1_first

    beziers[0] = (p0_first, c1_first, c2_first, p1_first)

    # --- Traitement du segment de fin (p0_last, c1_last, c2_last, p1_last) ---
    p0_last, c1_last, c2_last, p1_last = beziers[-1]
    
    vec_p0_p1_last = ns_sub(p1_last, p0_last)
    len_p0_p1_last = distance(NSPoint(0, 0), vec_p0_p1_last)

    if len_p0_p1_last < MIN_SEGMENT_LENGTH:
        # Segment trop court: forcer C2 = P1 pour faire une ligne droite
        if distance(c2_last, p1_last) > 0.1:
            c2_last = p1_last
            clamped_points['end'] = p1_last
    elif len_p0_p1_last > 1e-6:
        max_c2_len = len_p0_p1_last * PINCH_FACTOR
        vec_p1_c2 = ns_sub(c2_last, p1_last)

        unit_vec_p0_p1_last = ns_div(vec_p0_p1_last, len_p0_p1_last)
        unit_vec_p1_p0_last = ns_mul(unit_vec_p0_p1_last, -1) 
        dot_product = vec_p1_c2.x * unit_vec_p1_p0_last.x + vec_p1_c2.y * unit_vec_p1_p0_last.y
        
        if dot_product < 0:
            c2_last = ns_add(p1_last, ns_mul(unit_vec_p1_p0_last, max_c2_len))
            clamped_points['end'] = c2_last
        else:
            vec_p1_c2_limited = ns_limit_length(vec_p1_c2, max_c2_len)
            c2_last_new = ns_add(p1_last, vec_p1_c2_limited)
            if distance(c2_last_new, c2_last) > 0.1:
                c2_last = c2_last_new
                clamped_points['end'] = c2_last

    beziers[-1] = (p0_last, c1_last, c2_last, p1_last)
    
    # Renvoyer les beziers modifiés et les points de contrôle modifiés pour le repère
    return beziers, clamped_points['start'], clamped_points['end']


# ----------------------------------------------------------
# Palette intégrée : ToolVariables
# ----------------------------------------------------------
class BallpointToolVariables(PalettePlugin):
    dialog = objc.IBOutlet()
    thicknessSlider = objc.IBOutlet()
    smoothingSlider = objc.IBOutlet()
    thicknessLabel = objc.IBOutlet()
    smoothingLabel = objc.IBOutlet()
    thickness = 20.0
    smoothing = 6
    @objc.python_method
    def settings(self):
        self.name = Glyphs.localize({'en': 'Ballpoint settings','fr': 'Paramètres du stylo','de': 'Kugelschreiber-Einstellungen','es': 'Ajustes del boli','zh': '笔设置','ja': 'ペンの設定','pt': 'Configurações da caneta','it': 'Impostazioni della penna','nl': 'Peninstellingen','ko': '펜 설정','ru': 'Настройки пера',})
        self.loadNib('IBdialog', __file__)
        self.dialog.setController_(self)
    @objc.python_method
    def start(self):
        Glyphs.addCallback(self.update, UPDATEINTERFACE)
    @objc.python_method
    def __del__(self):
        Glyphs.removeCallback(self.update)
    def minHeight(self): return 120
    def maxHeight(self): return 120
    @objc.IBAction
    def thicknessChanged_(self, sender):
        self.thickness = round(sender.floatValue())
        if Ballpoint.instance:
            Ballpoint.instance.strokeWidth = self.thickness
        self.update(None)
    @objc.IBAction
    def smoothingChanged_(self, sender):
        self.smoothing = round(sender.floatValue())
        if Ballpoint.instance:
            Ballpoint.instance.simplifyEpsilon = DEFAULT_SIMPLIFY_EPSILON * (1.25 ** self.smoothing)
        self.update(None)
    @objc.python_method
    def update(self, sender):
        labels = Glyphs.localize({'en': {'thickness_label': 'Thickness:', 'smoothing_label': 'Smoothing:'},'fr': {'thickness_label': 'Épaisseur :', 'smoothing_label': 'Lissage :'},'de': {'thickness_label': 'Dicke:', 'smoothing_label': 'Glättung:'},'es': {'thickness_label': 'Grosor:', 'smoothing_label': 'Suavizado:'},'zh': {'thickness_label': '粗细:', 'smoothing_label': '平滑度:'},'ja': {'thickness_label': '太さ:', 'smoothing_label': 'スムージング:'},'pt': {'thickness_label': 'Espessura:', 'smoothing_label': 'Suavização:'},'it': {'thickness_label': 'Spessore:', 'smoothing_label': 'Levigatura:'},'nl': {'thickness_label': 'Dikte:', 'smoothing_label': 'Gladmaken:'},'ko': {'thickness_label': '두께:', 'smoothing_label': '매끄럽게:'},'ru': {'thickness_label': 'Толщина:', 'smoothing_label': 'Сглаживание:'},})
        if self.thicknessLabel:
            self.thicknessLabel.setStringValue_(f'{labels["thickness_label"]} {int(self.thickness)}')
        if self.smoothingLabel:
            self.smoothingLabel.setStringValue_(f'{labels["smoothing_label"]} {int(self.smoothing)}')
    @objc.python_method
    def __file__(self):
        return __file__
# ----------------------------------------------------------
# Ballpoint Tool principal
# ----------------------------------------------------------
class Ballpoint(SelectTool):
    instance = None

    @objc.python_method
    def settings(self):
        self.name = Glyphs.localize({'en': 'Ballpoint','fr': 'Stylo','de': 'Kugelschreiber','es': 'Bolígrafo','zh': '圆珠笔','ja': 'ボールペン','pt': 'Caneta','it': 'Penna','nl': 'Balpen','ko': '볼펜','ru': 'Шариковая ручка',})
        # Note: L'icône doit être placée dans le même dossier que le plugin
        icon_path = os.path.join(os.path.dirname(__file__), "BallpointTool.pdf")
        highlight_path = os.path.join(os.path.dirname(__file__), "BallpointToolHighlight.pdf")
        
        # Vérification si les fichiers PDF existent (peut échouer si les fichiers .pdf ne sont pas présents)
        if os.path.exists(icon_path):
            self.default_image = NSImage.alloc().initByReferencingFile_(icon_path)
        else:
            self.default_image = None
            
        if os.path.exists(highlight_path):
            self.active_image = NSImage.alloc().initByReferencingFile_(highlight_path)
        else:
            self.active_image = None

        self.tool_bar_image = self.default_image
        self.toolbarIconName = "BallpointTool"
        self.keyboardShortcut = 'Y'
        self.toolbarPosition = 182
        self.strokeWidth = DEFAULT_STROKE_WIDTH
        self.simplifyEpsilon = DEFAULT_SIMPLIFY_EPSILON
        self.minDistance = MIN_DISTANCE
        self.roundCaps = True
        Ballpoint.instance = self

    @objc.python_method
    def start(self):
        self.points = []
        self.lastPoint = None

    @objc.python_method
    def activate(self):
        self.tool_bar_image = self.active_image

    @objc.python_method
    def deactivate(self):
        self.tool_bar_image = self.default_image

    def mouseDown_(self, theEvent):
        view = self.editViewController().graphicView()
        loc = view.getActiveLocation_(theEvent)
        self.points = [loc]
        self.lastPoint = loc

        # --- Détection du type d'entrée ---
        self.usingStylus = False
        try:
            if hasattr(theEvent, "pressure"):
                pressure = theEvent.pressure()

                if 0.0 < pressure < 1.0:
                    self.usingStylus = True
            elif hasattr(theEvent, "tabletPointingDeviceType"):
                devType = theEvent.tabletPointingDeviceType()
                # 1 = Pen, 2 = Cursor, 3 = Eraser
                if devType in (1, 3):
                    self.usingStylus = True
        except Exception as e:
            print("Device detection failed:", e)

        # Ajustement des paramètres en fonction du périphérique
        if self.usingStylus:
            self.minDistance = 2.0
        else:
            self.minDistance = 4.0
            view.setNeedsDisplay_(True)

    def mouseDragged_(self, theEvent):
        if not self.lastPoint:
            return
        view = self.editViewController().graphicView()
        loc = view.getActiveLocation_(theEvent)
        if distance(self.lastPoint, loc) >= self.minDistance:
            self.points.append(loc)
            self.lastPoint = loc
            view.setNeedsDisplay_(True)

    def mouseUp_(self, theEvent):
        objc.super(Ballpoint, self).mouseUp_(theEvent)
        view = self.editViewController().graphicView()
        if len(self.points) < 2:
            self.points = []
            self.lastPoint = None
            view.setNeedsDisplay_(True)
            return
        layer = view.activeLayer()
        path = GSPath()
        path.closed = False
        
        # 1. Pré-simplification des extrémités 
        pre_simplified_points = simplify_ends(self.points, num_points_to_process=5, epsilon_ends=1.0)
        
        # 2. Simplification RDP globale
        simplified_points = rdp_simplify(pre_simplified_points, self.simplifyEpsilon)
        if len(simplified_points) < 2:
            simplified_points = pre_simplified_points[:]
        
        # 3. Nettoyage des points d'ancrage près des extrémités (distance=5.0)
        simplified_points = cleanup_endpoints(simplified_points, min_distance=5.0)

        # 4. Trim et Bézier
        simplified_points = trim_ends(simplified_points, trim_length=self.strokeWidth * 0.05)
        beziers = b_spline_to_bezier(simplified_points)
        
        if not beziers:
            for pt in simplified_points:
                path.nodes.append(GSNode(NSPoint(round(pt.x), round(pt.y)), type=GSLINE))
            layer.paths.append(path)
            self.points = []
            self.lastPoint = None
            view.setNeedsDisplay_(True)
            return
        
        # 5. Correction du clampage des tangentes 
        beziers, _, _ = apply_clamping(beziers)
        
        first = True
        previous_c2 = None
        
        # 6. Construction des nœuds Glyphs avec alignement C1 symétrique
        for i, (p0, c1, c2, p1) in enumerate(beziers):
            p0_rounded = NSPoint(round(p0.x), round(p0.y))
            p1_rounded = NSPoint(round(p1.x), round(p1.y))

            if first:
                path.nodes.append(GSNode(p0_rounded, type=GSLINE))
                path.nodes[-1].smooth = True 
                
                path.nodes.append(GSNode(c1, type=GSOFFCURVE))
                path.nodes.append(GSNode(c2, type=GSOFFCURVE))
                path.nodes.append(GSNode(p1_rounded, type=GSCURVE))
                path.nodes[-1].smooth = True
                
                previous_c2 = c2 
                first = False
            else:
                c1_new = make_tangent_symmetric(p0_rounded, previous_c2) 
                
                path.nodes.append(GSNode(c1_new, type=GSOFFCURVE))
                path.nodes.append(GSNode(c2, type=GSOFFCURVE))
                path.nodes.append(GSNode(p1_rounded, type=GSCURVE))
                path.nodes[-1].smooth = True
                
                previous_c2 = c2 
        
        # 7. Attributs de trait
        try:
            path.attributes["strokeWidth"] = self.strokeWidth
            path.attributes["lineCapStart"] = 1
            path.attributes["lineCapEnd"] = 1
        except:
            pass
        layer.paths.append(path)
        self.points = []
        self.lastPoint = None
        view.setNeedsDisplay_(True)
    
    @objc.python_method
    def background(self, layer):
        if len(self.points) < 2:
            return

        # 1. Prétraitement des points (identique à mouseUp)
        pre_simplified_points = simplify_ends(self.points, num_points_to_process=5, epsilon_ends=1.0)
        simplified_points_bg = rdp_simplify(pre_simplified_points, self.simplifyEpsilon)
        simplified_points_bg = cleanup_endpoints(simplified_points_bg, min_distance=5.0)
        simplified_points_bg = trim_ends(simplified_points_bg, trim_length=self.strokeWidth * 0.05)
        beziers = b_spline_to_bezier(simplified_points_bg)
        
        if not beziers:
            return

        # 2. Application du clamping (pour obtenir les points modifiés)
        beziers_clamped, start_clamped_point, end_clamped_point = apply_clamping(beziers)

        # 3. Dessin du chemin temporaire
        color = NSColor.blackColor().colorWithAlphaComponent_(0.5)
        color.set()
        bezier = NSBezierPath.bezierPath()
        bezier.setLineWidth_(self.strokeWidth)
        bezier.setLineCapStyle_(1)
        
        bezier.moveToPoint_(beziers_clamped[0][0])
        for p0, c1, c2, p1 in beziers_clamped:
            bezier.curveToPoint_controlPoint1_controlPoint2_(p1, c1, c2)
        bezier.stroke()
        
        # 4. Affichage des repères visuels
        dot_color = NSColor.redColor()
        dot_color.set()
        dot_radius = 4.0

        if start_clamped_point:
            # Dessine un cercle rouge sur le point de contrôle de début modifié
            dot_path = NSBezierPath.bezierPathWithOvalInRect_(((start_clamped_point.x - dot_radius), (start_clamped_point.y - dot_radius), dot_radius * 2, dot_radius * 2))
            dot_path.fill()
            
        if end_clamped_point:
            # Dessine un cercle rouge sur le point de contrôle de fin modifié
            dot_path = NSBezierPath.bezierPathWithOvalInRect_(((end_clamped_point.x - dot_radius), (end_clamped_point.y - dot_radius), dot_radius * 2, dot_radius * 2))
            dot_path.fill()

    @objc.python_method
    def __file__(self):
        return __file__