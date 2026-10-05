using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Drawing;
using System.IO;
using System.Linq;
using System.Text.Json;
using System.Text.RegularExpressions;
using System.Windows.Forms;

namespace DescarConector.Monitor;

public partial class Form1 : Form
{
    // 1) Log del servicio
    // Nota: hoy es un único archivo fijo. Si mañana lo rotás por día (ConectorService_yyyy-MM-dd.log),
    // el monitor lo va a elegir automáticamente si existe.
    private string _serviceLogPath = @"\\192.168.0.47\DescarConector\ConectorService.log";

    // 2) Log del ScriptPrincipal (se deriva dinámicamente de la carpeta M-BOM)
    private string? _scriptPrincipalLogPath;
    private string? _scriptJsonLogPath;

    private long _posService = 0;
    private long _posPrincipal = 0;
    private long _posJson = 0;

    private string? _serviceLogActualPath;

    private readonly ConectorStatus _status = new();

    // =======================
    // Protheus (UI por tabla)
    // =======================
    private string? _lastSb1Flow;
    private Severity _lastSb1Severity = Severity.Ok;

    private string? _lastSg1Flow;
    private Severity _lastSg1Severity = Severity.Ok;

    private string? _lastSg2Flow;
    private Severity _lastSg2Severity = Severity.Ok;

    // =======================
    // Auxiliares de parseo
    // =======================

    // SB1 ScriptPrincipal: mapear "[SB1 JSON FINAL] codigo=..." -> "[SB1][PUT] Código de estado: X"
    private readonly Queue<string> _sb1CodigoQueue = new();
    private string? _sb1UltimoCodigoAsociado;

    // Progreso MBOM (scoping): SB1 JSON FINAL trae tag [MBOM] => lista esperada
    private readonly HashSet<string> _sb1ExpectedMbom = new(StringComparer.OrdinalIgnoreCase);
    private readonly HashSet<string> _sb1DoneMbom = new(StringComparer.OrdinalIgnoreCase);

    // Progreso MBOM: SG1 esperados (fantasmas)
    private readonly HashSet<string> _sg1ExpectedMbom = new(StringComparer.OrdinalIgnoreCase);
    private readonly HashSet<string> _sg1DoneMbom = new(StringComparer.OrdinalIgnoreCase);
    private bool _sg1CapturingExpected = false;
    private int _sg1ExpectedTarget = 0;

    // Progreso BOP
    private readonly HashSet<string> _bopDoneFiles = new(StringComparer.OrdinalIgnoreCase);
    private bool _bopStageStarted = false;

    // Estado de endpoints Protheus
    private EstadoEndpoint _healthEstado   = EstadoEndpoint.SinDatos;
    private EstadoEndpoint _protheusEstado = EstadoEndpoint.SinDatos;

    // Downtime tracking: cuándo se cayó y tiempo total acumulado en sesión
    private DateTime? _healthCaidoDesde;
    private DateTime? _protheusCaidoDesde;
    private TimeSpan _healthTiempoTotal = TimeSpan.Zero;
    private TimeSpan _protheusTiempoTotal = TimeSpan.Zero;

    // Supresión de falso "Inactivo" durante exportación de BOPs (los 500/timeout puntuales
    // durante la ráfaga de exportación suelen resolverse con reintento y no son una caída real)
    private bool _exportandoBopsAnterior = false;
    private DateTime? _exportBopsFinalizadoEn;
    private static readonly TimeSpan GraciaPostExportacion = TimeSpan.FromSeconds(60);

    // Conectividad con el servidor de red (\\192.168.0.47\...)
    private bool _servidorAlcanzable = true;
    private DateTime? _sinConexionDesde;
    private static readonly TimeSpan UmbralAvisoSinConexion = TimeSpan.FromSeconds(10);

    // Error al leer appsettings.json (se avisa una vez, no interrumpe el arranque)
    private string? _configLoadError;

    // Último error inesperado del monitor (se muestra en el banner superior en vez de pisar otras labels)
    private string? _monitorError;

    // Log aparte con historial de caídas/recuperaciones de HEALTH y Endpoints (Protheus)
    private static readonly string DowntimeLogPath = Path.Combine(AppContext.BaseDirectory, "ProtheusDowntime.log");
    private static readonly object DowntimeLogLock = new();

    // Contexto último SG2 para interpretar Body (ej. alias SH1)
    private string? _sg2LastCtxProd;
    private string? _sg2LastCtxVerb;
    private int _sg2LastCtxCode;

    // Contexto SG1 (para armar un flujo más útil desde ScriptPrincipal)
    private string? _sg1CtxProducto;
    private readonly Dictionary<string, int> _sg1LastPostByProducto = new(StringComparer.OrdinalIgnoreCase);

    // SG1 ScriptPrincipal: POST409 -> PUT
    private readonly Dictionary<(string mod, string product), int> _postPendientePut = new();

    // SG2/SH3 ScriptPrincipal: POST -> PUT por producto
    private readonly Dictionary<string, int> _sg2LastPostByProducto = new();

    // ConectorService.log (Web Service.exe): a veces el status no trae producto -> guardamos contexto último producto visto
    private readonly Dictionary<string, string> _svcLastProductoByMod = new(StringComparer.OrdinalIgnoreCase);

    // Último archivo MBOM visto (se re-aplica en Estructura creada: por si viene antes en el log)
    private string? _pendingMbomFile;

    // Errores BOP
    private int _bopErrorCount = 0;
    private string? _lastBopError;

    private List<string> _colaMbom = new();

    // =======================
    // Colores UI
    // =======================
    private static readonly Color ClrBlue      = Color.FromArgb(45,  109, 232);
    private static readonly Color ClrTeal      = Color.FromArgb(12,  166, 120);
    private static readonly Color ClrOrange    = Color.FromArgb(230,  95,  20);
    private static readonly Color ClrTextPrim  = Color.FromArgb(25,  40,  70);
    private static readonly Color ClrTextSec   = Color.FromArgb(110, 120, 140);
    private static readonly Color ClrTrack     = Color.FromArgb(218, 223, 232);
    private static readonly Color ClrBg        = Color.FromArgb(242, 244, 248);
    private static readonly Color ClrCard      = Color.FromArgb(255, 255, 255);
    private static readonly Color ClrSep       = Color.FromArgb(210, 215, 228);
    private static readonly Color ClrAccent    = Color.FromArgb(40,  75, 145);

    // =======================
    // Regex (SERVICIO - estado MBOM/BOP)
    // =======================
    private static readonly Regex RxMbom = new(@"Procesando MBOM:\s*(?<file>.+?\.plmxml)",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    private static readonly Regex RxBop = new(@"Procesando BOP:\s*(?<file>.+?\.xml)",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    private static readonly Regex RxEstructura = new(@"Estructura creada:\s*(?<path>[A-Z]:\\.+)",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    private static readonly Regex RxMbomOk = new(@"Procesamiento OK para:\s*(?<path>[A-Z]:\\.+?\.plmxml)",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    // =======================
    // Regex (SCRIPT PRINCIPAL) - progreso
    // =======================
    // Listado de ítems SB1 desde SQL: "[SB1 SQL][MBOM] codigo_hijo=XXX | ..."
    private static readonly Regex RxSb1SqlMbom = new(@"^\uFEFF?\d{4}-\d{2}-\d{2} .*?\[SB1 SQL\]\[MBOM\]\s+codigo_hijo=(?<codigo>[^\s|]+)",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    private static readonly Regex RxSg1InicioMasivo = new(@"^\uFEFF?\d{4}-\d{2}-\d{2} .*?\[SG1-POST\]\s+Iniciando\s+envío\s+masivo\.\s+Productos:\s*(?<count>\d+)",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    private static readonly Regex RxSg1Enviando = new(@"^\uFEFF?\d{4}-\d{2}-\d{2} .*?\[SG1\]\[POST\]\s+Enviando\s+estructura\s+->\s+producto:\s*(?<prod>\S+)",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    private static readonly Regex RxSg1DbUpdate = new(@"^\uFEFF?\d{4}-\d{2}-\d{2} .*?\[SG1-DB\]\s+ActualizarBase:\s+estado=(?<code>\d{3})\s+codigo=(?<cod>\S+)",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    private static readonly Regex RxBopActual = new(@"^\uFEFF?\d{4}-\d{2}-\d{2} .*?\[SB1\]\[BOP\].*?BOPs\s+disponibles=(?<total>\d+).*?Actual=(?<bop>P-[^\s\|]+)",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    private static readonly Regex RxBopProcesado = new(@"^\uFEFF?\d{4}-\d{2}-\d{2} .*?BOP\s+Procesado:\s*(?<file>P-[^\s]+\.xml)",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    // JSON_ScriptPrincipal.log
    private static readonly Regex RxJsonResp = new(@"^\uFEFF?\d{4}-\d{2}-\d{2} .*?\[(?<mod>SB1|SG1|SG2SH3)\]\[(?<verb>POST|PUT)\]\s+RESPUESTA\s+JSON\s+para\s+(?<cod>\S+)\s+\(HTTP\s+(?<code>\d{3})\):",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    // Body de SG2SH3 (ScriptPrincipal)
    private static readonly Regex RxSg2Body = new(@"^\uFEFF?\d{4}-\d{2}-\d{2} .*?\[SG2SH3\]\[(?<verb>POST|PUT)\]\s+Body:\s+(?<body>.+)$",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    // =======================
    // Regex (SERVICIO - Web Service.exe)
    // =======================
    // Ej: 2026-01-02 ... - [Web Service.exe] [SB1][PUT] Protheus respondi¢ 500...
    private static readonly Regex RxSvcWebServicePrefix = new(
        @"^\uFEFF?\d{4}-\d{2}-\d{2} .*? - \[Web Service\.exe\]\s+(?<msg>.*)$",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    // Capturar producto/codigo cuando exista en línea (para dar contexto a status posteriores)
    // Ej: [SB1][PUT] Modificando producto -> codigo: 450053, descripcion: ...
    private static readonly Regex RxSvcCodigoSb1 = new(
        @"^\[(?<mod>SB1)\]\[(?<verb>POST|PUT)\].*?\bcodigo:\s*(?<cod>[^,\s]+)",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    // SG1: Enviando POST para producto XXX...
    private static readonly Regex RxSvcSg1Producto = new(
        @"^\[SG1-POST(?:-[A-Z]+)?\].*?\bproducto\s+(?<prod>[A-Z0-9_\-]+)",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    // Retry health / 5xx (tolerante a encoding: respondi¢/respondió)
    // Ej: [SB1][PUT] Protheus respondi¢ 500. Reintentando ... Intento #1
    private static readonly Regex RxSvcRetry = new(
        @"^\[(?<mod>SB1|SG1|SG2SH3)\]\[(?<verb>POST|PUT)\]\s+Protheus\s+respon.*?\s+(?<code>\d{3})\b.*?Intento\s*#(?<attempt>\d+)",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    // Respuesta JSON (opcional; hoy no la mostramos, pero sirve si querés extraer message)
    private static readonly Regex RxSvcResp = new(
        @"^\[(?<mod>SB1|SG1|SG2SH3)\]\[(?<verb>POST|PUT)\]\s+Respuesta:\s+(?<body>.+)$",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    // SG2SH3 ya trae producto/verb/code
    private static readonly Regex RxSvcSg2Arrow = new(
        @"^\[SG2SH3\]\[(?<verb>POST|PUT)\]\s+->\s+(?<code>\d{3})\s+(?<reason>[^|]+)\|\s+producto=(?<prod>\S+)\s*$",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    // =======================
    // Regex (SCRIPT PRINCIPAL)
    // =======================
    private static readonly Regex RxPrincipalTimestamp = new(@"^\uFEFF?\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}\.\d{3}\s+-\s+",
        RegexOptions.Compiled);

    // SB1 (ScriptPrincipal.log) - identifica qué producto se está enviando
    private static readonly Regex RxSb1PostEnviando = new(@"^\uFEFF?\d{4}-\d{2}-\d{2} .*?\[SB1\]\[POST\]\s+Enviando producto -> codigo:\s*(?<codigo>[^,\s]+)",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    // SB1 (ScriptPrincipal.log) - código de estado del POST (para el caso 201 directo, sin PUT)
    private static readonly Regex RxSb1PostStatus = new(@"^\uFEFF?\d{4}-\d{2}-\d{2} .*?\[SB1\]\[POST\]\s+Código de estado:\s*(?<code>\d{3})\b",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    private static readonly Regex RxSb1PutStatus = new(@"^\uFEFF?\d{4}-\d{2}-\d{2} .*?\[SB1\]\[PUT\]\s+Código de estado:\s*(?<code>\d{3})\b",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    private static readonly Regex RxSb1PutResp = new(@"^\uFEFF?\d{4}-\d{2}-\d{2} .*?\[SB1\]\[PUT\]\s+Respuesta:\s*(?<body>.+)$",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    // SG1 (ScriptPrincipal.log)
    private static readonly Regex RxSg1Post409 = new(@"^\uFEFF?\d{4}-\d{2}-\d{2} .*?\[(?<tag>SG1-POST(?:-[A-Z]+)?)\].*?\b409\b.*?\spara\s+(?<product>[^\.]+?)\.\s+Se acumula para PUT",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    private static readonly Regex RxSg1PostOk = new(@"^\uFEFF?\d{4}-\d{2}-\d{2} .*?\[(?<tag>SG1-POST(?:-[A-Z]+)?)\]\s+POST OK para\s+(?<product>[^:]+):\s*(?<code>\d{3})\b",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    private static readonly Regex RxSg1PutOk = new(@"^\uFEFF?\d{4}-\d{2}-\d{2} .*?\[SG1-PUT\]\s+PUT OK para producto\s+(?<product>[^:]+):\s*(?<code>\d{3})\b",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    private static readonly Regex RxSg1PutErr = new(@"^\uFEFF?\d{4}-\d{2}-\d{2} .*?\[SG1-PUT\]\s+PUT ERROR.*?producto\s+(?<product>[^:]+):\s*(?<code>\d{3})\b",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    // SG1 (ScriptPrincipal.log) - formato actual (Enviando / Código de estado / DB)
    private static readonly Regex RxSg1PostStatusLine = new(@"^\uFEFF?\d{4}-\d{2}-\d{2} .*?\[SG1\]\[POST\]\s+Código de estado:\s*(?<code>\d{3})\b",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    // Estado de endpoints Protheus
    private static readonly Regex RxHealthError = new(@"\[HEALTH\].*(ERROR|TIMEOUT)",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    private static readonly Regex RxInternalServerError = new(@"Internal Server Error",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    private static readonly Regex RxHttpTimeout = new(@"HttpClient\.Timeout",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    // Timestamp al inicio de línea: "yyyy-MM-dd HH:mm:ss.fff - "
    private static readonly Regex RxLineTs = new(@"^(?:\uFEFF)?(?<ts>\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2})\.\d{3}\s+-\s+",
        RegexOptions.Compiled);

    // Errores BOP: captura cualquier línea tagged [BOP] con ERROR, o patrones de error explícitos durante BOP
    private static readonly Regex RxBopError = new(
        @"\[BOP\].*?(?:ERROR|Error|error)|\[SB1\]\[BOP\].*?(?:ERROR|Error)|(?:ERROR|Error).*?\[BOP\]",
        RegexOptions.Compiled);

    // SG2/SH3 (ScriptPrincipal.log)
    private static readonly Regex RxSg2Arrow = new(@"^\uFEFF?\d{4}-\d{2}-\d{2} .*?\[SG2SH3\]\[(?<verb>POST|PUT)\]\s+->\s+(?<code>\d{3})\s+(?<reason>[^|]+)\|\s+producto=(?<prod>\S+)\s*$",
        RegexOptions.Compiled | RegexOptions.IgnoreCase);

    private string _claimedFolderPath = @"\\192.168.0.47\tctemp\_CLAIMED";

    private List<(string Local, string Network)> _pathMappings = new()
    {
        (@"E:\DescarConector\", @"\\192.168.0.47\DescarConector\"),
        (@"E:\Siemens\tctemp\", @"\\192.168.0.47\tctemp\"),
    };

    private readonly System.Windows.Forms.Timer _timer;

    private readonly ToolTip _toolTip = new();

    public Form1()
    {
        Text    = "Descar Conector — Monitor";
        Width   = 1000;
        Height  = 822;
        BackColor     = ClrBg;
        Font          = new Font("Segoe UI", 9f);
        DoubleBuffered = true;
        FormBorderStyle = FormBorderStyle.FixedSingle;
        MaximizeBox     = false;
        StartPosition   = FormStartPosition.CenterScreen;

        const int x = 16, w = 952, pad = 14, gap = 10;
        int y = 12;

        // ─────────────────────────────────────────────
        // BANNER DE ESTADO (sin conexión / error del monitor)
        // ─────────────────────────────────────────────
        var lblBanner = new Label
        {
            Left = x, Top = y, Width = w, Height = 26, Name = "lblBanner",
            TextAlign = ContentAlignment.MiddleCenter, AutoSize = false,
            Font = new Font("Segoe UI", 9f, FontStyle.Bold),
            Visible = false
        };
        Controls.Add(lblBanner);
        y += 26 + gap;

        // ─────────────────────────────────────────────
        // SECCIÓN MBOM
        // ─────────────────────────────────────────────
        {
            int cy = pad;
            var card = MakeCard(x, y, w, 120);
            card.Controls.Add(MakeSectionHeader("MBOM", pad, cy, w - pad * 2)); cy += 22;

            var lblMbomProg = MakeLabel("lblMbomProg", pad, cy, w - pad * 2); cy += 18;
            var lblMbomSub  = MakeLabel("lblMbomSub",  pad, cy, w - pad * 2, ClrTextSec); cy += 20;

            var lblTagSb1 = MakeTag("SB1", pad, cy + 1);
            var pbSb1 = new FlatProgressBar { Left = pad + 42, Top = cy, Width = w - pad * 2 - 42, Height = 14, Name = "pbSb1", BarColor = ClrBlue };
            cy += 19;

            var lblTagSg1 = MakeTag("SG1", pad, cy + 1);
            var pbSg1 = new FlatProgressBar { Left = pad + 42, Top = cy, Width = w - pad * 2 - 42, Height = 14, Name = "pbSg1", BarColor = ClrTeal };

            card.Controls.AddRange(new Control[] { lblMbomProg, lblMbomSub, lblTagSb1, pbSb1, lblTagSg1, pbSg1 });
            y += 120 + gap;
        }

        // ─────────────────────────────────────────────
        // SECCIÓN BOP
        // ─────────────────────────────────────────────
        {
            int cy = pad;
            var card = MakeCard(x, y, w, 82);
            card.Controls.Add(MakeSectionHeader("BOP", pad, cy, w - pad * 2)); cy += 22;

            var lblBopProg = MakeLabel("lblBopProg", pad, cy, w - pad * 2); cy += 18;

            var lblTagBop = MakeTag("BOP", pad, cy + 1);
            var pbBop = new FlatProgressBar { Left = pad + 42, Top = cy, Width = w - pad * 2 - 42, Height = 14, Name = "pbBop", BarColor = ClrOrange };

            card.Controls.AddRange(new Control[] { lblBopProg, lblTagBop, pbBop });
            y += 82 + gap;
        }

        // ─────────────────────────────────────────────
        // CONTEXTO
        // ─────────────────────────────────────────────
        {
            int cy = pad;
            var card = MakeCard(x, y, w, 106);
            card.Controls.Add(MakeSectionHeader("Contexto", pad, cy, w - pad * 2)); cy += 22;

            var lblXml      = MakeLabel("lblXml",      pad, cy, w - pad * 2);            cy += 18;
            var lblMbom     = MakeLabel("lblMbom",     pad, cy, w - pad * 2);            cy += 18;
            var lblMbomPath = MakeLabel("lblMbomPath", pad, cy, w - pad * 2 - 110, ClrTextSec);
            var btnOpen = new Button
            {
                Left = w - pad - 98, Top = cy - 1, Width = 90, Height = 24,
                Name = "btnOpen", Text = "Abrir",
                FlatStyle = FlatStyle.Flat,
                BackColor = ClrCard, ForeColor = ClrBlue,
                Cursor = Cursors.Hand
            };
            btnOpen.FlatAppearance.BorderColor = ClrBlue;
            btnOpen.Click += (_, __) => AbrirCarpetaMbom();

            card.Controls.AddRange(new Control[] { lblXml, lblMbom, lblMbomPath, btnOpen });
            y += 106 + gap;
        }

        // ─────────────────────────────────────────────
        // COLA DE MBOM PENDIENTES
        // ─────────────────────────────────────────────
        {
            int cy = pad;
            var card = MakeCard(x, y, w, 122);
            var lblColaTitle = new Label
            {
                Left = pad, Top = cy, Width = w - pad * 2, Name = "lblColaTitle",
                Text = "MBOM en cola",
                Font = new Font("Segoe UI", 9f, FontStyle.Bold),
                ForeColor = ClrAccent, AutoSize = false
            };
            cy += 22;

            var lbCola = new ListBox
            {
                Left = pad, Top = cy, Width = w - pad * 2, Height = 122 - cy - pad,
                Name = "lbCola",
                BorderStyle = BorderStyle.None,
                BackColor = ClrCard,
                ForeColor = ClrTextPrim,
                SelectionMode = SelectionMode.None,
                HorizontalScrollbar = false,
                IntegralHeight = false,
            };

            card.Controls.AddRange(new Control[] { lblColaTitle, lbCola });
            y += 122 + gap;
        }

        // ─────────────────────────────────────────────
        // ÚLTIMO ESTADO PROTHEUS
        // ─────────────────────────────────────────────
        {
            int cy = pad;
            var card = MakeCard(x, y, w, 124);
            card.Controls.Add(MakeSectionHeader("Último estado Protheus", pad, cy, w - pad * 2)); cy += 22;

            var lblSb1 = MakeLabel("lblProSb1", pad, cy, w - pad * 2); cy += 20;
            var lblSg1 = MakeLabel("lblProSg1", pad, cy, w - pad * 2); cy += 20;
            var lblSg2 = MakeLabel("lblProSg2", pad, cy, w - pad * 2); cy += 20;
            var lblBopErrors = new Label
            {
                Left = pad, Top = cy, Width = w - pad * 2, Height = 18, Name = "lblBopErrors",
                AutoSize = false, AutoEllipsis = true, ForeColor = ClrTextSec
            };

            card.Controls.AddRange(new Control[] { lblSb1, lblSg1, lblSg2, lblBopErrors });
            y += 124 + gap;
        }

        // ─────────────────────────────────────────────
        // PIE: ACTUALIZACIÓN + ENDPOINTS + VERSIÓN
        // ─────────────────────────────────────────────
        Controls.Add(MakeSeparator(x, y, w)); y += 10;

        var lblUpd = MakeLabel("lblUpd", x, y, w, ClrTextSec); y += 22;

        var lblEstadoTitulo = new Label
        {
            Left = x, Top = y + 3, Width = 140,
            Text = "Estado Protheus:", ForeColor = ClrTextPrim, AutoSize = false
        };
        var lblHealthStatus = new Label
        {
            Left = x + 148, Top = y, Width = 178, Height = 26, Name = "lblHealthStatus",
            TextAlign = ContentAlignment.MiddleCenter, AutoSize = false,
            Font = new Font("Segoe UI", 9f, FontStyle.Bold)
        };
        var lblProtheusStatus = new Label
        {
            Left = x + 336, Top = y, Width = 198, Height = 26, Name = "lblProtheusStatus",
            TextAlign = ContentAlignment.MiddleCenter, AutoSize = false,
            Font = new Font("Segoe UI", 9f, FontStyle.Bold)
        };
        var lblBopExportando = new Label
        {
            Left = x + 542, Top = y, Width = w - 542, Height = 26, Name = "lblBopExportando",
            TextAlign = ContentAlignment.MiddleCenter, AutoSize = false,
            Font = new Font("Segoe UI", 9f, FontStyle.Bold),
            Visible = false
        };
        y += 32;

        var lblHealthDowntime = new Label
        {
            Left = x, Top = y, Width = w, Height = 16, Name = "lblHealthDowntime",
            AutoSize = false, ForeColor = Color.DimGray
        };
        y += 18;
        var lblProtheusDowntime = new Label
        {
            Left = x, Top = y, Width = w, Height = 16, Name = "lblProtheusDowntime",
            AutoSize = false, ForeColor = Color.DimGray
        };
        y += 20;

        var version = typeof(Form1).Assembly.GetName().Version;
        var versionText = version != null ? $"{version.Major}.{version.Minor}.{version.Build}" : "1.0.0";
        var lblVersion = new Label
        {
            Left = x, Top = y, Width = w, Height = 16, Name = "lblVersion",
            Text = $"Descar Conector — Monitor  ·  v{versionText}",
            TextAlign = ContentAlignment.MiddleRight,
            ForeColor = ClrTextSec, AutoSize = false
        };

        Controls.AddRange(new Control[]
        {
            lblUpd,
            lblEstadoTitulo, lblHealthStatus, lblProtheusStatus, lblBopExportando,
            lblHealthDowntime, lblProtheusDowntime, lblVersion
        });

        _toolTip.SetToolTip(lblHealthStatus,
            "Gris = todavía no llegó ningún dato de este endpoint en la sesión actual.\nVerde = responde OK.  Rojo = no responde.");
        _toolTip.SetToolTip(lblProtheusStatus,
            "Gris = todavía no llegó ningún dato de este endpoint en la sesión actual.\nVerde = responde OK.  Rojo = no responde.");

        LoadConfig();

        _timer = new System.Windows.Forms.Timer { Interval = 1000 };
        _timer.Tick += (_, __) => TickUpdate();
        _timer.Start();
    }

    // ─────────────────────────────────────────────
    // Helpers de construcción de UI
    // ─────────────────────────────────────────────
    private static Label MakeLabel(string name, int x, int y, int w, Color? fore = null)
        => new Label
        {
            Left = x, Top = y, Width = w, Height = 18, Name = name,
            AutoSize = false, AutoEllipsis = true,
            ForeColor = fore ?? ClrTextPrim
        };

    private static Label MakeTag(string text, int x, int y)
        => new Label
        {
            Left = x, Top = y, Width = 38, AutoSize = false,
            Text = text, ForeColor = ClrTextSec
        };

    private static Label MakeSectionHeader(string text, int x, int y, int w)
        => new Label
        {
            Left = x, Top = y, Width = w, AutoSize = false,
            Text = text,
            Font = new Font("Segoe UI", 9f, FontStyle.Bold),
            ForeColor = ClrAccent
        };

    private static Panel MakeSeparator(int x, int y, int w)
        => new Panel { Left = x, Top = y, Width = w, Height = 1, BackColor = ClrSep };

    // Tarjeta blanca con borde sutil; devuelve el panel interno donde se agregan los controles
    // (usar coordenadas relativas al panel interno, no al form).
    private Panel MakeCard(int x, int y, int w, int h)
    {
        var outer = new Panel { Left = x, Top = y, Width = w, Height = h, BackColor = ClrSep };
        var inner = new Panel { Left = 1, Top = 1, Width = w - 2, Height = h - 2, BackColor = ClrCard };
        outer.Controls.Add(inner);
        Controls.Add(outer);
        return inner;
    }

    private void LoadConfig()
    {
        var configPath = Path.Combine(AppContext.BaseDirectory, "appsettings.json");
        if (!File.Exists(configPath)) return;
        try
        {
            var doc = JsonDocument.Parse(File.ReadAllText(configPath));
            var root = doc.RootElement;
            if (root.TryGetProperty("ServiceLogPath", out var sp) && sp.GetString() is string sval)
                _serviceLogPath = sval;
            if (root.TryGetProperty("ClaimedFolderPath", out var cp) && cp.GetString() is string cval)
                _claimedFolderPath = cval;
            if (root.TryGetProperty("PathMappings", out var mappings))
            {
                _pathMappings.Clear();
                foreach (var m in mappings.EnumerateArray())
                {
                    var local   = m.GetProperty("Local").GetString();
                    var network = m.GetProperty("Network").GetString();
                    if (local != null && network != null)
                        _pathMappings.Add((local, network));
                }
            }
        }
        catch (Exception ex)
        {
            _configLoadError = $"Error leyendo appsettings.json ({ex.Message}) — usando valores por defecto";
        }
    }

    private string TranslatePath(string path)
    {
        foreach (var (local, network) in _pathMappings)
            if (path.StartsWith(local, StringComparison.OrdinalIgnoreCase))
                return network + path[local.Length..];
        return path;
    }

    private void AbrirCarpetaMbom()
    {
        if (string.IsNullOrWhiteSpace(_status.MbomFolderPath))
        {
            MessageBox.Show(this, "Todavía no se detectó ninguna carpeta M-BOM en el log.",
                "Descar Conector — Monitor", MessageBoxButtons.OK, MessageBoxIcon.Information);
            return;
        }

        if (!Directory.Exists(_status.MbomFolderPath))
        {
            MessageBox.Show(this, $"No se pudo acceder a la carpeta:\n{_status.MbomFolderPath}\n\nVerificá la conexión de red.",
                "Descar Conector — Monitor", MessageBoxButtons.OK, MessageBoxIcon.Warning);
            return;
        }

        try
        {
            Process.Start(new ProcessStartInfo
            {
                FileName = _status.MbomFolderPath,
                UseShellExecute = true
            });
        }
        catch (Exception ex)
        {
            MessageBox.Show(this, $"No se pudo abrir la carpeta:\n{ex.Message}",
                "Descar Conector — Monitor", MessageBoxButtons.OK, MessageBoxIcon.Error);
        }
    }

    private bool _tickRunning = false;

    private async void TickUpdate()
    {
        if (_tickRunning) return;
        _tickRunning = true;
        try
        {
            await System.Threading.Tasks.Task.Run(() =>
            {
                ActualizarConexionServidor();
                LeerNuevasLineasServicioYParsear();
                LeerNuevasLineasScriptPrincipalYParsear();
                LeerNuevasLineasScriptJsonYParsear();
                ActualizarProgresoBopFallbackPorCarpetas();
                ActualizarColaMbom();
            });
            _monitorError = null;
            PintarUI();
        }
        catch (Exception ex)
        {
            _monitorError = $"Error en el monitor: {ex.Message}";
            PintarBanner();
        }
        finally
        {
            _tickRunning = false;
        }
    }

    // Verifica si el share de red del servidor (\\192.168.0.47\...) responde.
    // No confundir con "el log todavía no existe": esto chequea la RAÍZ del share.
    private void ActualizarConexionServidor()
    {
        bool alcanzable;
        try
        {
            var root = Path.GetPathRoot(_serviceLogPath);
            alcanzable = string.IsNullOrWhiteSpace(root) || Directory.Exists(root);
        }
        catch
        {
            alcanzable = false;
        }

        if (alcanzable)
        {
            _servidorAlcanzable = true;
            _sinConexionDesde = null;
        }
        else
        {
            _sinConexionDesde ??= DateTime.Now;
            _servidorAlcanzable = false;
        }
    }

    // ==========================================================
    // 1) LECTOR LOG SERVICIO
    // ==========================================================

    private string ResolveServiceLogPath()
    {
        try
        {
            var dir = Path.GetDirectoryName(_serviceLogPath);
            var baseName = Path.GetFileNameWithoutExtension(_serviceLogPath);
            var ext = Path.GetExtension(_serviceLogPath);

            if (!string.IsNullOrWhiteSpace(dir))
            {
                var dated = Path.Combine(dir, $"{baseName}_{DateTime.Now:yyyy-MM-dd}{ext}");
                if (File.Exists(dated))
                    return dated;
            }

            return _serviceLogPath;
        }
        catch
        {
            return _serviceLogPath;
        }
    }

    private void LeerNuevasLineasServicioYParsear()
    {
        var path = ResolveServiceLogPath();
        if (!File.Exists(path)) return;

        if (!string.Equals(_serviceLogActualPath, path, StringComparison.OrdinalIgnoreCase))
        {
            _serviceLogActualPath = path;
            _posService = 0;
        }

        using var fs = new FileStream(path, FileMode.Open, FileAccess.Read, FileShare.ReadWrite);
        if (fs.Length < _posService) _posService = 0;

        // Primera carga: escanear todo el archivo para encontrar el último "Estructura creada:"
        // y establecer el contexto de carpeta/MBOM aunque sea antiguo.
        if (_posService == 0 && string.IsNullOrWhiteSpace(_status.MbomFolderPath))
            BuscarContextoInicial(fs);

        const long maxInitialRead = 5 * 1024 * 1024; // 5 MB
        if (_posService == 0 && fs.Length > maxInitialRead)
            _posService = fs.Length - maxInitialRead;

        fs.Position = _posService;
        using var sr = new StreamReader(fs);

        string? line;
        while ((line = sr.ReadLine()) != null)
        {
            ParseLineServicio(line);
        }

        _posService = fs.Position;
    }

    private void BuscarContextoInicial(FileStream fs)
    {
        fs.Position = 0;
        string? ultimaEstructura = null;
        using var sr = new StreamReader(fs, System.Text.Encoding.UTF8, true, 65536, leaveOpen: true);
        string? line;
        while ((line = sr.ReadLine()) != null)
        {
            if (RxEstructura.IsMatch(line))
                ultimaEstructura = line;
        }
        if (ultimaEstructura != null)
            ParseLineServicio(ultimaEstructura);
    }

    private void ParseLineServicio(string line)
    {
        _status.LastLogUpdate = DateTime.Now;

        // --- Estado XML actual + carpeta MBOM
        var m1 = RxMbom.Match(line);
        if (m1.Success)
        {
            _pendingMbomFile = m1.Groups["file"].Value.Trim();
            _status.CurrentXml = _pendingMbomFile;
            _status.Phase = "MBOM";
            _status.CurrentMbomFile = _pendingMbomFile;
            _status.CurrentBopFile = null; // nuevo ciclo MBOM, BOP viejo no aplica
        }

        var m2 = RxBop.Match(line);
        if (m2.Success)
        {
            _status.CurrentXml = m2.Groups["file"].Value.Trim();
            _status.Phase = "BOP";
            _status.CurrentBopFile = _status.CurrentXml;
        }

        var m3 = RxEstructura.Match(line);
        if (m3.Success)
        {
            var newFolder = TranslatePath(m3.Groups["path"].Value.Trim());
            if (!Directory.Exists(newFolder)) goto afterEstructura;
            if (!string.Equals(newFolder, _status.MbomFolderPath, StringComparison.OrdinalIgnoreCase))
            {
                _status.MbomFolderPath = newFolder;
                _status.MbomFolderName = Path.GetFileName(_status.MbomFolderPath.TrimEnd('\\'));
                _status.MbomDone = false;

                _scriptPrincipalLogPath = Path.Combine(_status.MbomFolderPath, "ScriptPrincipal.log");
                _scriptJsonLogPath = Path.Combine(_status.MbomFolderPath, "JSON_ScriptPrincipal.log");
                _posPrincipal = 0;
                _posJson = 0;

                // reset parseos
                _postPendientePut.Clear();
                _sb1CodigoQueue.Clear();
                _sb1UltimoCodigoAsociado = null;
                _sg2LastPostByProducto.Clear();
                _svcLastProductoByMod.Clear();
                _sg1LastPostByProducto.Clear();
                _sg1CtxProducto = null;
                _sg2LastCtxProd = null;
                _sg2LastCtxVerb = null;
                _sg2LastCtxCode = 0;

                // reset progreso
                _sb1ExpectedMbom.Clear();
                _sb1DoneMbom.Clear();
                _sg1ExpectedMbom.Clear();
                _sg1DoneMbom.Clear();
                _sg1CapturingExpected = false;
                _sg1ExpectedTarget = 0;

                _bopDoneFiles.Clear();
                _bopStageStarted = false;

                _status.Sb1Total = 0;
                _status.Sg1Total = 0;
                _status.BopTotal = 0;
                _status.Sb1Done = 0;
                _status.Sg1Done = 0;
                _status.BopDone = 0;
                _status.MbomCurrentTable = "-";
                _status.BopCurrentTable = "-";

                _lastSb1Flow = null;
                _lastSg1Flow = null;
                _lastSg2Flow = null;

                _lastSb1Severity = Severity.Ok;
                _lastSg1Severity = Severity.Ok;
                _lastSg2Severity = Severity.Ok;

                // El .plmxml está en la misma carpeta que ScriptPrincipal.log
                _pendingMbomFile = null;
                var plmxml = Directory.GetFiles(_status.MbomFolderPath!, "*.plmxml", SearchOption.TopDirectoryOnly).FirstOrDefault();
                _status.CurrentMbomFile = plmxml != null ? Path.GetFileName(plmxml) : _status.MbomFolderName;
                _status.CurrentXml = _status.CurrentMbomFile;
                _status.Phase = "MBOM";
                _status.CurrentBopFile = null;
            }
        }
        afterEstructura:;

        var m4 = RxMbomOk.Match(line);
        if (m4.Success && !string.IsNullOrWhiteSpace(_status.MbomFolderPath))
        {
            _status.MbomDone = true;
        }

        // Solo marcar inactivo con líneas recientes; evita rojo falso al releer logs históricos
        var lineDtSvc = ParseLineDt(line);
        var esRecienteSvc = (DateTime.Now - lineDtSvc).TotalMinutes < 3;

        if (esRecienteSvc && RxHealthError.IsMatch(line) && _healthEstado != EstadoEndpoint.Inactivo)
            MarcarHealthInactivo();
        if (esRecienteSvc && (RxInternalServerError.IsMatch(line) || RxHttpTimeout.IsMatch(line)) && _protheusEstado != EstadoEndpoint.Inactivo)
            MarcarProtheusInactivo();

        // --- NUEVO: Protheus desde ConectorService.log (prefijo [Web Service.exe])
        ParseLineServicio_Protheus(line);
    }

    private void ParseLineServicio_Protheus(string line)
    {
        var mw = RxSvcWebServicePrefix.Match(line);
        if (!mw.Success) return;

        var msg = mw.Groups["msg"].Value.Trim();
        if (string.IsNullOrWhiteSpace(msg)) return;

        // Capturar contexto de producto/código si aparece (SB1)
        var mcodSb1 = RxSvcCodigoSb1.Match(msg);
        if (mcodSb1.Success)
        {
            var cod = mcodSb1.Groups["cod"].Value.Trim();
            if (!string.IsNullOrWhiteSpace(cod))
                _svcLastProductoByMod["SB1"] = cod;
            // no return: puede venir en la misma línea con status (raro, pero posible)
        }

        // Capturar contexto de producto para SG1 si aparece
        var msg1 = RxSvcSg1Producto.Match(msg);
        if (msg1.Success)
        {
            var prod = msg1.Groups["prod"].Value.Trim();
            if (!string.IsNullOrWhiteSpace(prod))
                _svcLastProductoByMod["SG1"] = prod;
        }

        // SG2/SH3 en formato flecha
        var mSg2 = RxSvcSg2Arrow.Match(msg);
        if (mSg2.Success)
        {
            var verb = mSg2.Groups["verb"].Value.ToUpperInvariant();
            var code = int.Parse(mSg2.Groups["code"].Value);
            var prod = mSg2.Groups["prod"].Value.Trim();

            if (verb == "POST")
            {
                _sg2LastPostByProducto[prod] = code;
                _lastSg2Flow = $"{prod}: POST {code}";
                _lastSg2Severity = CalcularSeveridadDesdeCodigo(code, esPost: true);
                return;
            }

            if (_sg2LastPostByProducto.TryGetValue(prod, out var postCode))
            {
                _sg2LastPostByProducto.Remove(prod);
                _lastSg2Flow = $"{prod}: POST {postCode} ? PUT {code}";
                _lastSg2Severity = CalcularSeveridadFlujo(postCode, code);
            }
            else
            {
                _lastSg2Flow = $"{prod}: PUT {code}";
                _lastSg2Severity = CalcularSeveridadDesdeCodigo(code, esPost: false);
            }

            return;
        }

        // Retry / health (típico cuando Protheus está 5xx o caído)
        var mr = RxSvcRetry.Match(msg);
        if (mr.Success)
        {
            var modRaw = mr.Groups["mod"].Value.ToUpperInvariant();   // SB1 / SG1 / SG2SH3
            var verb = mr.Groups["verb"].Value.ToUpperInvariant();    // POST/PUT
            var code = int.Parse(mr.Groups["code"].Value);
            var attempt = int.Parse(mr.Groups["attempt"].Value);

            var modUi = modRaw == "SG2SH3" ? "SG2/SH3" : modRaw;

            _svcLastProductoByMod.TryGetValue(modUi, out var prodCtx);
            if (string.IsNullOrWhiteSpace(prodCtx))
                prodCtx = _svcLastProductoByMod.TryGetValue(modRaw, out var p2) ? p2 : "";

            var flow = string.IsNullOrWhiteSpace(prodCtx)
                ? $"{verb} {code} (reintento #{attempt})"
                : $"{prodCtx}: {verb} {code} (reintento #{attempt})";

            var sev = CalcularSeveridadDesdeCodigo(code, esPost: verb == "POST");

            ApplyFlow(modUi, flow, sev);
            return;
        }

        // Respuesta (si algún día querés mostrar message, se puede parsear acá)
        var mresp = RxSvcResp.Match(msg);
        if (mresp.Success)
        {
            // hoy no lo mostramos en UI
            return;
        }
    }

    private void ApplyFlow(string modUi, string flow, Severity sev)
    {
        switch (modUi.ToUpperInvariant())
        {
            case "SB1":
                _lastSb1Flow = flow;
                _lastSb1Severity = sev;
                break;

            case "SG1":
                _lastSg1Flow = flow;
                _lastSg1Severity = sev;
                break;

            case "SG2/SH3":
            case "SG2SH3":
                _lastSg2Flow = flow;
                _lastSg2Severity = sev;
                break;
        }
    }

    // ==========================================================
    // 2) LECTOR LOG SCRIPT PRINCIPAL
    // ==========================================================
    private void LeerNuevasLineasScriptPrincipalYParsear()
    {
        if (string.IsNullOrWhiteSpace(_scriptPrincipalLogPath)) return;
        if (!File.Exists(_scriptPrincipalLogPath)) return;

        using var fs = new FileStream(_scriptPrincipalLogPath, FileMode.Open, FileAccess.Read, FileShare.ReadWrite);
        if (fs.Length < _posPrincipal) _posPrincipal = 0;

        // En la primera lectura del log no marcamos endpoints como inactivos:
        // evita falsos rojos al releer el historial completo al reabrir la app.
        bool esLecturaInicial = _posPrincipal == 0;

        fs.Position = _posPrincipal;
        using var sr = new StreamReader(fs);

        string? line;
        while ((line = sr.ReadLine()) != null)
        {
            if (!RxPrincipalTimestamp.IsMatch(line))
                continue;

            ParseLineScriptPrincipal(line, esLecturaInicial);
        }

        _posPrincipal = fs.Position;
    }

    private void ParseLineScriptPrincipal(string line, bool esLecturaInicial = false)
    {
        // Solo marcar inactivo en lecturas incrementales (no al releer el historial al abrir)
        if (!esLecturaInicial)
        {
            var lineDtPrincipal = ParseLineDt(line);
            if ((DateTime.Now - lineDtPrincipal).TotalMinutes < 3
                && (RxInternalServerError.IsMatch(line) || RxHttpTimeout.IsMatch(line)) && _protheusEstado != EstadoEndpoint.Inactivo)
                MarcarProtheusInactivo();
        }

        // Detección de errores BOP
        if (RxBopError.IsMatch(line))
        {
            _bopErrorCount++;
            // Extraer el mensaje útil: quitar el timestamp prefix
            var msg = RxPrincipalTimestamp.Replace(line, "").Trim();
            _lastBopError = msg.Length > 120 ? msg[..120] + "…" : msg;
        }

        // ==========================
        // Progreso MBOM (SB1 esperados — listado SQL previo al envío)
        // ==========================
        var mSb1List = RxSb1SqlMbom.Match(line);
        if (mSb1List.Success)
        {
            var codigo = mSb1List.Groups["codigo"].Value.Trim();
            if (!string.IsNullOrWhiteSpace(codigo))
            {
                _sb1ExpectedMbom.Add(codigo);
                _status.Sb1Total = _sb1ExpectedMbom.Count;
            }
            // no return
        }

        // ==========================
        // Progreso BOP (inicio de archivo actual + total)
        // ==========================
        var mBopAct = RxBopActual.Match(line);
        if (mBopAct.Success)
        {
            if (!_bopStageStarted)
            {
                // Al entrar en fase BOP resetear estado de endpoints para no arrastrar
                // downtimes o estados del MBOM previo mientras el log aún no existe
                _healthEstado        = EstadoEndpoint.SinDatos;
                _protheusEstado      = EstadoEndpoint.SinDatos;
                _healthCaidoDesde    = null;
                _protheusCaidoDesde  = null;
            }
            _bopStageStarted = true;

            var total = int.Parse(mBopAct.Groups["total"].Value);
            _status.BopTotal = total;

            var bop = mBopAct.Groups["bop"].Value.Trim();
            if (!bop.EndsWith(".xml", StringComparison.OrdinalIgnoreCase))
                bop += ".xml";

            _status.CurrentBopFile = bop;
            _status.BopCurrentTable = "SB1";
            return;
        }

        // ==========================
        // Progreso BOP (fin de archivo)
        // ==========================
        var mBopDone = RxBopProcesado.Match(line);
        if (mBopDone.Success)
        {
            var file = mBopDone.Groups["file"].Value.Trim();
            if (!string.IsNullOrWhiteSpace(file))
            {
                _bopDoneFiles.Add(file);
                _status.BopDone = _bopDoneFiles.Count;
            }
            return;
        }

        // ==========================
        // Progreso MBOM (captura SG1 esperados)
        // ==========================
        if (!_bopStageStarted && _sg1ExpectedMbom.Count == 0)
        {
            var mStart = RxSg1InicioMasivo.Match(line);
            if (mStart.Success)
            {
                _sg1ExpectedTarget = int.Parse(mStart.Groups["count"].Value);
                _sg1CapturingExpected = _sg1ExpectedTarget > 0;
                if (_status.Sg1Total <= 0)
                    _status.Sg1Total = _sg1ExpectedTarget;
                // no return
            }
        }

        if (_sg1CapturingExpected)
        {
            var mProd = RxSg1Enviando.Match(line);
            if (mProd.Success)
            {
                var prod = mProd.Groups["prod"].Value.Trim();
                if (!string.IsNullOrWhiteSpace(prod))
                {
                    _sg1ExpectedMbom.Add(prod);
                    if (_sg1ExpectedMbom.Count >= _sg1ExpectedTarget)
                        _sg1CapturingExpected = false;
                }
                // no return
            }
        }

        // ==========================
        // SG1 (DB update => estado final por producto)
        // ==========================
        var mSg1Db = RxSg1DbUpdate.Match(line);
        if (mSg1Db.Success)
        {
            var code = int.Parse(mSg1Db.Groups["code"].Value);
            var cod = mSg1Db.Groups["cod"].Value.Trim();

            // tabla actual
            if (_bopStageStarted)
                _status.BopCurrentTable = "SG1";
            else
                _status.MbomCurrentTable = "SG1";

            // progreso MBOM SG1: sólo fantasmas esperados
            if (!_bopStageStarted && _sg1ExpectedMbom.Contains(cod) && (code == 200 || code == 201))
            {
                _sg1DoneMbom.Add(cod);
                _status.Sg1Done = _sg1DoneMbom.Count;
            }

            // flujo UI
            if (_sg1LastPostByProducto.TryGetValue(cod, out var postCode) && postCode == 409 && (code == 200 || code == 201))
            {
                _lastSg1Flow = $"{cod}: POST 409 ? PUT {code}";
                _lastSg1Severity = Severity.Ok;
            }
            else
            {
                _lastSg1Flow = $"{cod}: POST {code}";
                _lastSg1Severity = CalcularSeveridadDesdeCodigo(code, esPost: true);
            }

            return;
        }

        // ==========================
        // SG2/SH3 Body (para excepciones toleradas)
        // ==========================
        var mSg2Body = RxSg2Body.Match(line);
        if (mSg2Body.Success)
        {
            var body = mSg2Body.Groups["body"].Value;

            if (_sg2LastCtxCode == 400 && !string.IsNullOrWhiteSpace(body) && body.Contains("alias SH1", StringComparison.OrdinalIgnoreCase))
            {
                // Este 400 está aceptado por trazabilidad (no lo marcamos como error)
                _lastSg2Severity = Severity.Warning;
                if (!string.IsNullOrWhiteSpace(_sg2LastCtxProd) && !string.IsNullOrWhiteSpace(_sg2LastCtxVerb))
                    _lastSg2Flow = $"{_sg2LastCtxProd}: {_sg2LastCtxVerb} 400 (alias SH1)";
            }

            return;
        }

        // ==========================
        // SB1
        // ==========================

        // "Enviando producto -> codigo: XXX" — encola el código que está por enviarse
        var mSb1Cod = RxSb1PostEnviando.Match(line);
        if (mSb1Cod.Success)
        {
            var codigo = mSb1Cod.Groups["codigo"].Value.Trim();
            if (!string.IsNullOrWhiteSpace(codigo))
                _sb1CodigoQueue.Enqueue(codigo);

            if (_bopStageStarted)
                _status.BopCurrentTable = "SB1";
            else
                _status.MbomCurrentTable = "SB1";
            return;
        }

        // POST con código de estado — caso 201 (directo, sin PUT posterior)
        var mSb1Post = RxSb1PostStatus.Match(line);
        if (mSb1Post.Success)
        {
            var code = int.Parse(mSb1Post.Groups["code"].Value);
            if (code != 409) // 409 lo maneja el PUT handler; los demás cierran el ciclo aquí
            {
                var codigo = _sb1CodigoQueue.Count > 0 ? _sb1CodigoQueue.Dequeue() : "(desconocido)";
                _sb1UltimoCodigoAsociado = codigo;

                _lastSb1Flow = $"{codigo}: POST {code}";
                _lastSb1Severity = CalcularSeveridadDesdeCodigo(code, esPost: true);

                if (!_bopStageStarted && _sb1ExpectedMbom.Contains(codigo) && (code == 200 || code == 201))
                {
                    _sb1DoneMbom.Add(codigo);
                    _status.Sb1Done = _sb1DoneMbom.Count;
                }

                if (_bopStageStarted)
                    _status.BopCurrentTable = "SB1";
                else
                    _status.MbomCurrentTable = "SB1";
            }
            return;
        }

        // PUT con código de estado — caso 409→PUT (el código ya estaba en la cola desde el POST)
        var mSb1Put = RxSb1PutStatus.Match(line);
        if (mSb1Put.Success)
        {
            var code = int.Parse(mSb1Put.Groups["code"].Value);

            var codigo = _sb1CodigoQueue.Count > 0 ? _sb1CodigoQueue.Dequeue() : "(desconocido)";
            _sb1UltimoCodigoAsociado = codigo;

            _lastSb1Flow = $"{codigo}: POST 409 → PUT {code}";
            _lastSb1Severity = CalcularSeveridadFlujo(409, code);

            if (!_bopStageStarted && _sb1ExpectedMbom.Contains(codigo) && (code == 200 || code == 201))
            {
                _sb1DoneMbom.Add(codigo);
                _status.Sb1Done = _sb1DoneMbom.Count;
            }

            if (_bopStageStarted)
                _status.BopCurrentTable = "SB1";
            else
                _status.MbomCurrentTable = "SB1";
            return;
        }

        var _ = RxSb1PutResp.Match(line);
        if (_.Success)
        {
            // no mostramos body por ahora
            return;
        }

        // ==========================
        // SG1
        // ==========================

        // Formato actual: "Enviando estructura" => contexto
        var mSg1Send = RxSg1Enviando.Match(line);
        if (mSg1Send.Success)
        {
            var prod = mSg1Send.Groups["prod"].Value.Trim();
            if (!string.IsNullOrWhiteSpace(prod))
                _sg1CtxProducto = prod;

            if (_bopStageStarted)
                _status.BopCurrentTable = "SG1";
            else
                _status.MbomCurrentTable = "SG1";

            return;
        }

        // Formato actual: "Código de estado" (POST)
        var mSg1PostSt = RxSg1PostStatusLine.Match(line);
        if (mSg1PostSt.Success && !string.IsNullOrWhiteSpace(_sg1CtxProducto))
        {
            var code = int.Parse(mSg1PostSt.Groups["code"].Value);
            _sg1LastPostByProducto[_sg1CtxProducto] = code;

            _lastSg1Flow = $"{_sg1CtxProducto}: POST {code}";
            _lastSg1Severity = CalcularSeveridadDesdeCodigo(code, esPost: true);

            if (_bopStageStarted)
                _status.BopCurrentTable = "SG1";
            else
                _status.MbomCurrentTable = "SG1";

            return;
        }

        var m409 = RxSg1Post409.Match(line);
        if (m409.Success)
        {
            var product = m409.Groups["product"].Value.Trim();
            _postPendientePut[("SG1", product)] = 409;

            _lastSg1Flow = $"{product}: POST 409 ? PUT (pendiente)";
            _lastSg1Severity = Severity.Warning;
            return;
        }

        var mpok = RxSg1PostOk.Match(line);
        if (mpok.Success)
        {
            var product = mpok.Groups["product"].Value.Trim();
            var code = int.Parse(mpok.Groups["code"].Value);

            _lastSg1Flow = $"{product}: POST {code}";
            _lastSg1Severity = CalcularSeveridadDesdeCodigo(code, esPost: true);
            return;
        }

        var mputOk = RxSg1PutOk.Match(line);
        if (mputOk.Success)
        {
            var product = mputOk.Groups["product"].Value.Trim();
            var code = int.Parse(mputOk.Groups["code"].Value);

            _lastSg1Flow = $"{product}: POST 409 ? PUT {code}";
            _lastSg1Severity = CalcularSeveridadFlujo(409, code);

            _postPendientePut.Remove(("SG1", product));
            return;
        }

        var mputErr = RxSg1PutErr.Match(line);
        if (mputErr.Success)
        {
            var product = mputErr.Groups["product"].Value.Trim();
            var code = int.Parse(mputErr.Groups["code"].Value);

            _lastSg1Flow = $"{product}: POST 409 ? PUT {code} (ERROR)";
            _lastSg1Severity = CalcularSeveridadFlujo(409, code);

            _postPendientePut.Remove(("SG1", product));
            return;
        }

        // ==========================
        // SG2/SH3
        // ==========================
        var mSg2 = RxSg2Arrow.Match(line);
        if (mSg2.Success)
        {
            var verb = mSg2.Groups["verb"].Value.ToUpperInvariant();
            var code = int.Parse(mSg2.Groups["code"].Value);
            var prod = mSg2.Groups["prod"].Value.Trim();

            _sg2LastCtxVerb = verb;
            _sg2LastCtxCode = code;
            _sg2LastCtxProd = prod;

            if (_bopStageStarted)
                _status.BopCurrentTable = "SG2_SH3";

            if (verb == "POST")
            {
                _sg2LastPostByProducto[prod] = code;
                _lastSg2Flow = $"{prod}: POST {code}";
                _lastSg2Severity = CalcularSeveridadDesdeCodigo(code, esPost: true);
                return;
            }

            if (_sg2LastPostByProducto.TryGetValue(prod, out var postCode))
            {
                _sg2LastPostByProducto.Remove(prod);
                _lastSg2Flow = $"{prod}: POST {postCode} ? PUT {code}";
                _lastSg2Severity = CalcularSeveridadFlujo(postCode, code);
            }
            else
            {
                _lastSg2Flow = $"{prod}: PUT {code}";
                _lastSg2Severity = CalcularSeveridadDesdeCodigo(code, esPost: false);
            }

            return;
        }
    }

    // ==========================================================
    // 2.b) LECTOR JSON_ScriptPrincipal.log (para progreso SB1)
    // ==========================================================
    private void LeerNuevasLineasScriptJsonYParsear()
    {
        if (string.IsNullOrWhiteSpace(_scriptJsonLogPath)) return;
        if (!File.Exists(_scriptJsonLogPath)) return;

        using var fs = new FileStream(_scriptJsonLogPath, FileMode.Open, FileAccess.Read, FileShare.ReadWrite);
        if (fs.Length < _posJson) _posJson = 0;

        bool esLecturaInicialJson = _posJson == 0;

        fs.Position = _posJson;
        using var sr = new StreamReader(fs);

        string? line;
        while ((line = sr.ReadLine()) != null)
        {
            if (!RxPrincipalTimestamp.IsMatch(line))
                continue;

            // Solo marcar inactivo en lecturas incrementales
            if (!esLecturaInicialJson)
            {
                var lineDtJson = ParseLineDt(line);
                var esRecienteJson = (DateTime.Now - lineDtJson).TotalMinutes < 3;
                if (esRecienteJson && RxHealthError.IsMatch(line) && _healthEstado != EstadoEndpoint.Inactivo)
                    MarcarHealthInactivo();
                if (esRecienteJson && (RxInternalServerError.IsMatch(line) || RxHttpTimeout.IsMatch(line)) && _protheusEstado != EstadoEndpoint.Inactivo)
                    MarcarProtheusInactivo();
            }

            var m = RxJsonResp.Match(line);
            if (!m.Success) continue;

            var mod = m.Groups["mod"].Value.ToUpperInvariant();
            var cod = m.Groups["cod"].Value.Trim();
            var code = int.Parse(m.Groups["code"].Value);

            // Respuesta exitosa → endpoints activos; acumular tiempo caído antes de resetear
            if (code == 200 || code == 201)
            {
                var recoveryDt = DateTime.Now;
                if (_healthEstado == EstadoEndpoint.Inactivo && _healthCaidoDesde.HasValue)
                {
                    var duracion = recoveryDt - _healthCaidoDesde.Value;
                    _healthTiempoTotal += duracion;
                    _healthCaidoDesde = null;
                    LogDowntimeEvento("HEALTH", $"RECUPERADO (caído {FmtDowntime(duracion)})");
                }
                _healthEstado = EstadoEndpoint.Activo;

                if (_protheusEstado == EstadoEndpoint.Inactivo && _protheusCaidoDesde.HasValue)
                {
                    var duracion = recoveryDt - _protheusCaidoDesde.Value;
                    _protheusTiempoTotal += duracion;
                    _protheusCaidoDesde = null;
                    LogDowntimeEvento("Endpoints", $"RECUPERADO (caído {FmtDowntime(duracion)})");
                }
                _protheusEstado = EstadoEndpoint.Activo;
            }

            // Progreso MBOM SB1: sólo códigos del set esperado MBOM
            if (mod == "SB1" && _sb1ExpectedMbom.Contains(cod) && (code == 200 || code == 201))
            {
                _sb1DoneMbom.Add(cod);
                _status.Sb1Done = _sb1DoneMbom.Count;

                // total fallback por set
                if (_status.Sb1Total <= 0)
                    _status.Sb1Total = _sb1ExpectedMbom.Count;
            }
        }

        _posJson = fs.Position;
    }

    // ==========================================================
    // 3) PROGRESO BOP - fallback por carpetas
    // ==========================================================
    private void ActualizarColaMbom()
    {
        if (!Directory.Exists(_claimedFolderPath))
        {
            _colaMbom = new List<string>();
            return;
        }

        _colaMbom = Directory.GetDirectories(_claimedFolderPath)
            .OrderBy(carpeta => Path.GetFileName(carpeta))
            .Select(carpeta => Directory.GetFiles(carpeta, "*.plmxml").FirstOrDefault())
            .Where(f => f != null)
            .Select(f => Path.GetFileName(f!))
            .ToList();
    }

    private void ActualizarProgresoBopFallbackPorCarpetas()
    {
        if (string.IsNullOrWhiteSpace(_status.MbomFolderPath)) return;

        var pend = Path.Combine(_status.MbomFolderPath, "BOP_Pendientes");
        var proc = Path.Combine(_status.MbomFolderPath, "BOP_Procesadas");
        if (!Directory.Exists(pend) || !Directory.Exists(proc)) return;

        var pendCount = Directory.GetFiles(pend, "*.xml", SearchOption.TopDirectoryOnly).Length;
        var procCount = Directory.GetFiles(proc, "*.xml", SearchOption.TopDirectoryOnly).Length;

        _status.BopPendientes = pendCount;
        _status.BopProcesadas = procCount;
        _status.BopTotal = pendCount + procCount;

        // Solo actualizar BopDone cuando el log confirmó que arrancó la fase BOP;
        // no auto-activar _bopStageStarted desde carpetas para no romper el tracking de SG1 MBOM
        if (_bopStageStarted)
            _status.BopDone = Math.Max(procCount, _bopDoneFiles.Count);
    }

    // ==========================================================
    // 4) UI
    // ==========================================================
    // Banner superior: conexión perdida, error de config o error inesperado del monitor.
    // Se pinta aparte de PintarUI para poder mostrarse incluso si el resto de la lectura falló.
    private void PintarBanner()
    {
        var lbl = Controls.Find("lblBanner", true).FirstOrDefault() as Label;
        if (lbl == null) return;

        bool sinConexionSostenida = !_servidorAlcanzable && _sinConexionDesde.HasValue
            && (DateTime.Now - _sinConexionDesde.Value) >= UmbralAvisoSinConexion;

        if (!string.IsNullOrEmpty(_monitorError))
        {
            lbl.Text = $"⚠ {_monitorError}";
            lbl.BackColor = Color.FromArgb(200, 30, 30);
            lbl.ForeColor = Color.White;
            lbl.Visible = true;
        }
        else if (sinConexionSostenida)
        {
            lbl.Text = "⚠ Sin conexión con el servidor de red — verificá la conexión";
            lbl.BackColor = Color.FromArgb(200, 30, 30);
            lbl.ForeColor = Color.White;
            lbl.Visible = true;
        }
        else if (!string.IsNullOrEmpty(_configLoadError))
        {
            lbl.Text = $"⚠ {_configLoadError}";
            lbl.BackColor = Color.FromArgb(230, 160, 20);
            lbl.ForeColor = Color.FromArgb(60, 40, 0);
            lbl.Visible = true;
        }
        else
        {
            lbl.Visible = false;
        }
    }

    private void PintarUI()
    {
        PintarBanner();

        var lblMbomProg = Controls.Find("lblMbomProg", true).FirstOrDefault() as Label;
        var lblMbomSub = Controls.Find("lblMbomSub", true).FirstOrDefault() as Label;
        var pbSb1 = Controls.Find("pbSb1", true).FirstOrDefault() as FlatProgressBar;
        var pbSg1 = Controls.Find("pbSg1", true).FirstOrDefault() as FlatProgressBar;

        var lblBopProg = Controls.Find("lblBopProg", true).FirstOrDefault() as Label;
        var pbBop = Controls.Find("pbBop", true).FirstOrDefault() as FlatProgressBar;

        var lblXml = Controls.Find("lblXml", true).FirstOrDefault() as Label;
        var lblMbom = Controls.Find("lblMbom", true).FirstOrDefault() as Label;
        var lblMbomPath = Controls.Find("lblMbomPath", true).FirstOrDefault() as Label;

        var lblSb1 = Controls.Find("lblProSb1", true).FirstOrDefault() as Label;
        var lblSg1 = Controls.Find("lblProSg1", true).FirstOrDefault() as Label;
        var lblSg2 = Controls.Find("lblProSg2", true).FirstOrDefault() as Label;

        var lblUpd = Controls.Find("lblUpd", true).FirstOrDefault() as Label;

        // =====================
        // MBOM (SB1+SG1)
        // =====================
        var sb1Total = _status.Sb1Total;
        var sb1Done = _status.Sb1Done;
        var sg1Total = _status.Sg1Total;
        var sg1Done = _status.Sg1Done;

        var mbomTotal = sb1Total + sg1Total;
        var mbomDone = sb1Done + sg1Done;
        var mbomPct = mbomTotal > 0 ? (mbomDone * 100.0 / mbomTotal) : 0.0;

        var sb1Pct = sb1Total > 0 ? (sb1Done * 100.0 / sb1Total) : 0.0;
        var sg1Pct = sg1Total > 0 ? (sg1Done * 100.0 / sg1Total) : 0.0;

        if (lblMbomProg != null)
            lblMbomProg.Text = $"MBOM: {mbomDone}/{mbomTotal} ({mbomPct:0.0}%) | MBOM Actual: {_status.CurrentMbomFile ?? "-"} | Tabla: {_status.MbomCurrentTable}";

        if (lblMbomSub != null)
            lblMbomSub.Text = $"SB1: {sb1Done}/{sb1Total} ({sb1Pct:0.0}%) | SG1: {sg1Done}/{sg1Total} ({sg1Pct:0.0}%)";

        SetProgress(pbSb1, sb1Done, sb1Total);
        SetProgress(pbSg1, sg1Done, sg1Total);

        // =====================
        // BOP
        // =====================
        var bopTotal = _status.BopTotal;
        var bopDone = _status.BopDone;
        var bopPct = bopTotal > 0 ? (bopDone * 100.0 / bopTotal) : 0.0;

        if (lblBopProg != null)
            lblBopProg.Text = $"BOP: {bopDone}/{bopTotal} ({bopPct:0.0}%) | BOP Actual: {_status.CurrentBopFile ?? "-"} | Tabla: {_status.BopCurrentTable}";

        SetProgress(pbBop, bopDone, bopTotal);

        if (lblXml != null)
            lblXml.Text = $"XML actual ({_status.Phase}): {_status.CurrentXml ?? "-"}";

        if (lblMbom != null)
            lblMbom.Text = $"M-BOM origen: {_status.MbomFolderName ?? "-"}";

        if (lblMbomPath != null)
            lblMbomPath.Text = $"Ruta: {_status.MbomFolderPath ?? "-"}";

        var lbCola = Controls.Find("lbCola", true).FirstOrDefault() as ListBox;
        var lblColaTitle = Controls.Find("lblColaTitle", true).FirstOrDefault() as Label;
        if (lbCola != null)
        {
            // Armar lista de display sin tocar el control si no cambió (preserva posición del scroll)
            List<string> displayItems;
            if (!Directory.Exists(_claimedFolderPath))
                displayItems = new List<string> { "(carpeta no encontrada)" };
            else if (_colaMbom.Count == 0)
                displayItems = new List<string> { "(sin MBOM en cola)" };
            else
                displayItems = _colaMbom;

            bool igual = lbCola.Items.Count == displayItems.Count
                && Enumerable.Range(0, lbCola.Items.Count).All(i => lbCola.Items[i]?.ToString() == displayItems[i]);

            if (!igual)
            {
                int topIdx = lbCola.TopIndex;
                lbCola.BeginUpdate();
                lbCola.Items.Clear();
                foreach (var f in displayItems)
                    lbCola.Items.Add(f);
                lbCola.EndUpdate();
                if (topIdx > 0 && topIdx < lbCola.Items.Count)
                    lbCola.TopIndex = topIdx;
            }

            if (lblColaTitle != null)
                lblColaTitle.Text = _colaMbom.Count > 0
                    ? $"MBOM en cola  ({_colaMbom.Count})"
                    : "MBOM en cola";
        }

        if (lblSb1 != null)
        {
            lblSb1.Text = $"SB1: {_lastSb1Flow ?? "-"}";
            lblSb1.ForeColor = _lastSb1Severity switch
            {
                Severity.Error => Color.DarkRed,
                Severity.Warning => Color.DarkOrange,
                _ => SystemColors.ControlText
            };
        }

        if (lblSg1 != null)
        {
            lblSg1.Text = $"SG1: {_lastSg1Flow ?? "-"}";
            lblSg1.ForeColor = _lastSg1Severity switch
            {
                Severity.Error => Color.DarkRed,
                Severity.Warning => Color.DarkOrange,
                _ => SystemColors.ControlText
            };
        }

        if (lblSg2 != null)
        {
            lblSg2.Text = $"SG2/SH3: {_lastSg2Flow ?? "-"}";
            lblSg2.ForeColor = _lastSg2Severity switch
            {
                Severity.Error => Color.DarkRed,
                Severity.Warning => Color.DarkOrange,
                _ => SystemColors.ControlText
            };
        }

        var lblBopErrors = Controls.Find("lblBopErrors", true).FirstOrDefault() as Label;
        if (lblBopErrors != null)
        {
            if (_bopErrorCount == 0)
            {
                lblBopErrors.Text      = "BOP Errores: —";
                lblBopErrors.ForeColor = ClrTextSec;
            }
            else
            {
                lblBopErrors.Text      = $"BOP Errores: {_bopErrorCount}  |  Último: {_lastBopError ?? "-"}";
                lblBopErrors.ForeColor = Color.DarkRed;
            }
        }

        if (lblUpd != null)
            lblUpd.Text = $"Última actualización: {_status.LastLogUpdate:yyyy-MM-dd HH:mm:ss}";

        // Exportando mientras haya BOPs en carpeta y el log del script todavía no exista
        bool exportandoBops = _status.BopTotal > 0
            && (string.IsNullOrWhiteSpace(_scriptPrincipalLogPath) || !File.Exists(_scriptPrincipalLogPath));

        // Detectar el fin de la ráfaga de exportación para arrancar la ventana de gracia
        if (_exportandoBopsAnterior && !exportandoBops)
            _exportBopsFinalizadoEn = DateTime.Now;
        _exportandoBopsAnterior = exportandoBops;

        // Gris solo si exportando Y todavía no llegó ningún dato real; si ya hay 201s, mostrar estado real
        var healthDisplay = (exportandoBops && _healthEstado == EstadoEndpoint.SinDatos) ? EstadoEndpoint.SinDatos : _healthEstado;

        // Protheus: durante la exportación (y unos segundos después de que termine) los 500/timeout
        // puntuales suelen ser transitorios y se resuelven con reintento; no mostrar "Inactivo" falso
        // salvo que la caída persista más allá de la ventana de gracia post-exportación.
        bool enGraciaPostExportacion = _exportBopsFinalizadoEn.HasValue
            && (DateTime.Now - _exportBopsFinalizadoEn.Value) < GraciaPostExportacion;
        var protheusDisplay = (_protheusEstado == EstadoEndpoint.Inactivo && (exportandoBops || enGraciaPostExportacion))
            ? EstadoEndpoint.SinDatos
            : _protheusEstado;

        var lblHealthStatus = Controls.Find("lblHealthStatus", true).FirstOrDefault() as Label;
        if (lblHealthStatus != null)
        {
            lblHealthStatus.Text = healthDisplay switch
            {
                EstadoEndpoint.Activo   => "● HEALTH: Activo",
                EstadoEndpoint.Inactivo => "● HEALTH: Inactivo",
                _                       => "● HEALTH: Sin datos"
            };
            lblHealthStatus.BackColor = healthDisplay switch
            {
                EstadoEndpoint.Activo   => Color.LimeGreen,
                EstadoEndpoint.Inactivo => Color.Red,
                _                       => Color.Silver
            };
            lblHealthStatus.ForeColor = healthDisplay switch
            {
                EstadoEndpoint.Activo   => Color.DarkGreen,
                EstadoEndpoint.Inactivo => Color.White,
                _                       => Color.FromArgb(70, 70, 70)
            };
        }

        var lblProtheusStatus = Controls.Find("lblProtheusStatus", true).FirstOrDefault() as Label;
        if (lblProtheusStatus != null)
        {
            lblProtheusStatus.Text = protheusDisplay switch
            {
                EstadoEndpoint.Activo   => "● Endpoints: Activo",
                EstadoEndpoint.Inactivo => "● Endpoints: Inactivo",
                _                       => "● Endpoints: Sin datos"
            };
            lblProtheusStatus.BackColor = protheusDisplay switch
            {
                EstadoEndpoint.Activo   => Color.LimeGreen,
                EstadoEndpoint.Inactivo => Color.Red,
                _                       => Color.Silver
            };
            lblProtheusStatus.ForeColor = protheusDisplay switch
            {
                EstadoEndpoint.Activo   => Color.DarkGreen,
                EstadoEndpoint.Inactivo => Color.White,
                _                       => Color.FromArgb(70, 70, 70)
            };
        }

        var lblBopExportando = Controls.Find("lblBopExportando", true).FirstOrDefault() as Label;
        if (lblBopExportando != null)
        {
            lblBopExportando.Visible = exportandoBops;
            if (exportandoBops)
            {
                lblBopExportando.Text      = $"⏳  Exportando BOPs... ({_status.BopDone}/{_status.BopTotal})";
                lblBopExportando.BackColor = Color.FromArgb(255, 200, 80);
                lblBopExportando.ForeColor = Color.FromArgb(100, 60, 0);
            }
        }

        var now = DateTime.Now;

        var lblHealthDowntime = Controls.Find("lblHealthDowntime", true).FirstOrDefault() as Label;
        if (lblHealthDowntime != null)
        {
            if (exportandoBops && _healthEstado == EstadoEndpoint.SinDatos)
            {
                lblHealthDowntime.Text      = "HEALTH — Sin datos (exportando BOPs)";
                lblHealthDowntime.ForeColor = Color.DimGray;
            }
            else
            {
                var curDown   = _healthCaidoDesde.HasValue ? now - _healthCaidoDesde.Value : TimeSpan.Zero;
                var totalDown = _healthTiempoTotal + curDown;
                if (_healthCaidoDesde.HasValue)
                {
                    lblHealthDowntime.Text      = $"HEALTH — Caído hace: {FmtDowntime(curDown)}  |  Total caído sesión: {FmtDowntime(totalDown)}";
                    lblHealthDowntime.ForeColor = Color.DarkRed;
                }
                else
                {
                    lblHealthDowntime.Text      = $"HEALTH — Total caído sesión: {FmtDowntime(totalDown)}";
                    lblHealthDowntime.ForeColor = totalDown.TotalSeconds >= 1 ? Color.DarkOrange : Color.DimGray;
                }
            }
        }

        var lblProtheusDowntime = Controls.Find("lblProtheusDowntime", true).FirstOrDefault() as Label;
        if (lblProtheusDowntime != null)
        {
            if (protheusDisplay == EstadoEndpoint.SinDatos && _protheusEstado != EstadoEndpoint.SinDatos)
            {
                lblProtheusDowntime.Text      = "Endpoints — Verificando (posible transitorio durante exportación de BOPs)";
                lblProtheusDowntime.ForeColor = Color.DimGray;
            }
            else if (exportandoBops && _protheusEstado == EstadoEndpoint.SinDatos)
            {
                lblProtheusDowntime.Text      = "Endpoints — Sin datos (exportando BOPs)";
                lblProtheusDowntime.ForeColor = Color.DimGray;
            }
            else
            {
                var curDown   = _protheusCaidoDesde.HasValue ? now - _protheusCaidoDesde.Value : TimeSpan.Zero;
                var totalDown = _protheusTiempoTotal + curDown;
                if (_protheusCaidoDesde.HasValue)
                {
                    lblProtheusDowntime.Text      = $"Endpoints — Caído hace: {FmtDowntime(curDown)}  |  Total caído sesión: {FmtDowntime(totalDown)}";
                    lblProtheusDowntime.ForeColor = Color.DarkRed;
                }
                else
                {
                    lblProtheusDowntime.Text      = $"Endpoints — Total caído sesión: {FmtDowntime(totalDown)}";
                    lblProtheusDowntime.ForeColor = totalDown.TotalSeconds >= 1 ? Color.DarkOrange : Color.DimGray;
                }
            }
        }
    }

    // Extrae el DateTime de la línea de log (formato "yyyy-MM-dd HH:mm:ss.fff - ...").
    // Si la línea no tiene timestamp (ej. ConectorService.log) devuelve DateTime.Now.
    private static DateTime ParseLineDt(string line)
    {
        var m = RxLineTs.Match(line);
        if (m.Success && DateTime.TryParseExact(
                m.Groups["ts"].Value, "yyyy-MM-dd HH:mm:ss",
                System.Globalization.CultureInfo.InvariantCulture,
                System.Globalization.DateTimeStyles.None, out var dt))
            return dt;
        return DateTime.Now;
    }

    // Formatea un TimeSpan a texto legible: "2h 5m 30s", "5m 30s", "30s", o "—" si es cero.
    private static string FmtDowntime(TimeSpan ts)
    {
        if (ts.TotalSeconds < 1) return "—";
        if (ts.TotalHours >= 1)  return $"{(int)ts.TotalHours}h {ts.Minutes}m {ts.Seconds}s";
        if (ts.TotalMinutes >= 1) return $"{(int)ts.TotalMinutes}m {ts.Seconds}s";
        return $"{(int)ts.TotalSeconds}s";
    }

    // ==========================================================
    // Log de caídas de HEALTH / Endpoints (Protheus)
    // ==========================================================
    private static void LogDowntimeEvento(string modulo, string evento)
    {
        try
        {
            var linea = $"{DateTime.Now:yyyy-MM-dd HH:mm:ss} - {modulo}: {evento}{Environment.NewLine}";
            lock (DowntimeLogLock)
                File.AppendAllText(DowntimeLogPath, linea);
        }
        catch
        {
            // no bloquear el monitor si no se puede escribir el log de downtime
        }
    }

    private void MarcarHealthInactivo()
    {
        _healthEstado = EstadoEndpoint.Inactivo;
        _healthCaidoDesde = DateTime.Now;
        LogDowntimeEvento("HEALTH", "CAÍDO");
    }

    private void MarcarProtheusInactivo()
    {
        _protheusEstado = EstadoEndpoint.Inactivo;
        _protheusCaidoDesde = DateTime.Now;
        LogDowntimeEvento("Endpoints", "CAÍDO");
    }

    private static void SetProgress(FlatProgressBar? pb, int done, int total)
    {
        if (pb == null) return;
        if (total <= 0) { pb.Value = 0; pb.Maximum = 1; return; }
        pb.Maximum = Math.Max(1, total);
        pb.Value   = Math.Clamp(done, 0, pb.Maximum);
    }

    // ==========================================================
    // Severidad
    // ==========================================================
    private static Severity CalcularSeveridadFlujo(int postCode, int putCode)
    {
        if (postCode >= 500 || putCode >= 500) return Severity.Error;
        if ((postCode >= 400 && postCode != 409) || (putCode >= 400 && putCode != 409)) return Severity.Error;

        if (postCode == 409 && (putCode == 200 || putCode == 201)) return Severity.Ok;

        return Severity.Warning;
    }

    private static Severity CalcularSeveridadDesdeCodigo(int code, bool esPost)
    {
        if (code >= 500) return Severity.Error;
        if (code >= 400 && code != 409) return Severity.Error;

        if (esPost && code == 409) return Severity.Warning;
        return Severity.Ok;
    }
}

public sealed class ConectorStatus
{
    public string? CurrentXml { get; set; }
    public string Phase { get; set; } = "-";

    public string? CurrentMbomFile { get; set; }
    public string? CurrentBopFile { get; set; }

    public string MbomCurrentTable { get; set; } = "-";
    public string BopCurrentTable { get; set; } = "-";

    public string? MbomFolderPath { get; set; }
    public string? MbomFolderName { get; set; }
    public bool MbomDone { get; set; }

    // Progreso MBOM
    public int Sb1Total { get; set; }
    public int Sb1Done { get; set; }
    public int Sg1Total { get; set; }
    public int Sg1Done { get; set; }

    // Progreso BOP (por archivo)
    public int BopTotal { get; set; }
    public int BopDone { get; set; }

    // Progreso por carpetas
    public int BopPendientes { get; set; }
    public int BopProcesadas { get; set; }

    public DateTime LastLogUpdate { get; set; }
}

public enum Severity
{
    Ok = 0,
    Warning = 1,
    Error = 2
}

public enum EstadoEndpoint
{
    SinDatos = 0,
    Activo   = 1,
    Inactivo = 2
}

/// <summary>Barra de progreso plana y coloreada, dibujada a mano.</summary>
internal sealed class FlatProgressBar : Panel
{
    private int _max = 1;
    private int _val = 0;

    [System.ComponentModel.DesignerSerializationVisibility(System.ComponentModel.DesignerSerializationVisibility.Hidden)]
    public int Maximum
    {
        get => _max;
        set { _max = Math.Max(1, value); Invalidate(); }
    }

    [System.ComponentModel.DesignerSerializationVisibility(System.ComponentModel.DesignerSerializationVisibility.Hidden)]
    public int Value
    {
        get => _val;
        set { _val = Math.Clamp(value, 0, _max); Invalidate(); }
    }

    [System.ComponentModel.DesignerSerializationVisibility(System.ComponentModel.DesignerSerializationVisibility.Hidden)]
    public Color BarColor { get; set; } = Color.SteelBlue;

    public FlatProgressBar()
    {
        DoubleBuffered = true;
        BackColor = Color.FromArgb(218, 223, 232); // ClrTrack
    }

    protected override void OnPaint(PaintEventArgs e)
    {
        var g = e.Graphics;
        g.Clear(BackColor);

        if (_max > 0 && _val > 0)
        {
            float pct = (float)_val / _max;
            int fw = Math.Clamp((int)(Width * pct), 0, Width);
            if (fw > 0)
                using (var br = new SolidBrush(BarColor))
                    g.FillRectangle(br, 0, 0, fw, Height);
        }
    }
}
