[English](README.md) | **Español**

# clingo-magic-sets

Transformador **Dynamic Magic Sets (DMS)** para [Clingo](https://potassco.org/clingo/).

`dms.py` reescribe un programa ASP anotado con directivas `#magic pred/n` y
produce un programa equivalente que restringe el *grounding* (la eliminación de
variables) de los predicados ocultos seleccionados a los átomos relevantes para
la consulta implícita. Clingo no soporta Magic Sets de forma nativa; esta
herramienta lo aporta como preprocesador externo, operando sobre el AST
(Abstract Syntax Tree) de Clingo a través de su API de Python.

Es una implementación del algoritmo Dynamic Magic Sets de Alviano, Faber, Greco
y Leone (véase [Referencias](#referencias)), desarrollada como parte de un
Traballo Fin de Grao (Grao en Intelixencia Artificial, Universidade da Coruña).

## Requisitos

- Python ≥ 3.9
- [clingo](https://pypi.org/project/clingo/) (paquete Python de la API de Clingo)

```bash
pip install -r requirements.txt
```

## Uso

```bash
python dms.py entrada.lp [salida.lp]
```

Si no se indica fichero de salida, el programa transformado se escribe por
`stdout`. El resultado es un programa ASP estándar que puede pasarse
directamente a Clingo:

```bash
python dms.py examples/reach.lp reach_dms.lp
clingo reach_dms.lp
```

### Atajo: `dms-solve.sh`

El script `dms-solve.sh` encadena los dos pasos (transformar + resolver) en un
solo comando. Cualquier argumento tras el fichero de entrada se pasa tal cual a
`clingo`:

```bash
./dms-solve.sh examples/reach.lp              # transforma y resuelve
./dms-solve.sh examples/reach.lp 0 --stats    # todos los answer sets + estadísticas
./dms-solve.sh -o reach_dms.lp examples/reach.lp   # conserva el transformado
./dms-solve.sh -h                             # ayuda
```

Opciones: `-o FICHERO` guarda el programa transformado (por defecto usa un
temporal), `-k` conserva el temporal, `-q` modo silencioso. La variable de
entorno `PYTHON` permite elegir el intérprete.

## Formato de entrada

Se anota el programa con una o varias directivas `#magic`, que declaran los
predicados (MDB) a transformar:

```prolog
#magic reach/2.            % transforma reach/2

reach(X, Y) :- edge(X, Y).
reach(X, Z) :- reach(X, Y), edge(Y, Z).

query(X) :- source(X), reach(X, Y).
```

Solo los predicados declarados con `#magic` se reescriben; el resto del programa
se copia sin cambios (salvo las semillas que dependen de él).

## Ejemplos

El directorio [`examples/`](examples/) contiene programas de muestra:

| Fichero | Qué ilustra |
|---|---|
| `reach.lp` | Alcanzabilidad en grafos (caso conductor, adornado `bf`). |
| `sameGen.lp` | Misma generación (EDB desconectados, análisis de Sippu). |
| `factorial.lp`, `fibonacci.lp` | Recursión aritmética sin dominio explícito. |
| `area.lp` | Aritmética sin dominio (DMS como proveedor de *safety*). |
| `sat.lp` | Fórmulas como términos compuestos (functores, anónimas). |
| `member.lp` | Listas con sintaxis Prolog (`cons`). |

## Documentación

[`docs/DMS_ALGORITHM.md`](docs/DMS_ALGORITHM.md) describe la correspondencia
entre el algoritmo original y la implementación, y las decisiones de diseño
(SIPS EDB-first, aritmética segura, desanonimización de variables, chequeo de
estratificación).

## Referencias

- M. Alviano, W. Faber, G. Greco, N. Leone. *Magic Sets for Disjunctive Datalog
  Programs*. Artificial Intelligence 187–188 (2012) 156–192.
- F. Bancilhon, D. Maier, Y. Sagiv, J. D. Ullman. *Magic Sets and Other Strange
  Ways to Implement Logic Programs*. PODS 1986.

## Licencia

[MIT](LICENSE) © 2026 Marcelo Ferreiro Sánchez.
