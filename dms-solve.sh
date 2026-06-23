#!/usr/bin/env bash
#
# dms-solve.sh — transforma un programa ASP con DMS y lo resuelve con clingo.
#
# Aplica el transformador Dynamic Magic Sets (dms.py) sobre el programa de
# entrada y ejecuta clingo sobre el programa transformado resultante.
#
# Uso:
#   ./dms-solve.sh [-o salida.lp] [-k] [-q] entrada.lp [args de clingo...]
#
# Opciones:
#   -o FICHERO   guarda el programa transformado en FICHERO (por defecto: temporal).
#   -k           conserva el fichero transformado (no lo borra al terminar).
#   -q           silencioso: no imprime las cabeceras informativas.
#   -h           muestra esta ayuda.
#
# Cualquier argumento tras el fichero de entrada se pasa tal cual a clingo.
#
# Ejemplos:
#   ./dms-solve.sh examples/reach.lp
#   ./dms-solve.sh examples/reach.lp 0 --stats     # todos los answer sets + stats
#   ./dms-solve.sh -o reach_dms.lp examples/reach.lp
#
# La variable de entorno PYTHON permite elegir el intérprete (por defecto python3).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DMS="$SCRIPT_DIR/dms.py"
PYTHON="${PYTHON:-python3}"

OUT=""
KEEP=0
QUIET=0

usage() { sed -n '2,30p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; }

while getopts ":o:kqh" opt; do
  case "$opt" in
    o) OUT="$OPTARG" ;;
    k) KEEP=1 ;;
    q) QUIET=1 ;;
    h) usage; exit 0 ;;
    :) echo "Error: la opción -$OPTARG requiere un argumento." >&2; exit 2 ;;
    \?) echo "Error: opción desconocida -$OPTARG." >&2; usage >&2; exit 2 ;;
  esac
done
shift $((OPTIND - 1))

if [ $# -lt 1 ]; then
  echo "Error: falta el programa de entrada." >&2
  usage >&2
  exit 2
fi

INPUT="$1"; shift
CLINGO_ARGS=("$@")

if [ ! -f "$INPUT" ]; then
  echo "Error: no existe el fichero de entrada '$INPUT'." >&2
  exit 2
fi
command -v clingo >/dev/null 2>&1 || { echo "Error: 'clingo' no está en el PATH." >&2; exit 127; }

# Fichero de salida: el indicado con -o, o uno temporal autoeliminable.
CLEANUP=0
if [ -z "$OUT" ]; then
  OUT="$(mktemp --suffix=.lp)"
  [ "$KEEP" -eq 0 ] && CLEANUP=1
fi
cleanup() { [ "$CLEANUP" -eq 1 ] && rm -f "$OUT"; }
trap cleanup EXIT

log() { [ "$QUIET" -eq 0 ] && echo "$@" >&2 || true; }

log ">> Transformando '$INPUT' con DMS ..."
"$PYTHON" "$DMS" "$INPUT" "$OUT"
log ">> Programa transformado en '$OUT'"
log ">> Ejecutando clingo ${CLINGO_ARGS[*]:-} ..."
log ""

# Propaga el código de salida de clingo (10 = SAT, 20 = UNSAT, etc.).
clingo "$OUT" "${CLINGO_ARGS[@]}"
