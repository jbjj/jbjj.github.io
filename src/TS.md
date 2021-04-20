# TypeScript

  > https://www.typescriptlang.org

    JS + static type definitions

    TS is a typed superset of JavaScript that compiles to plain JavaScript.

---

## Linguagem

   > https://www.typescriptlang.org/docs/handbook/


### Primitive Types

#### Boolean
#### Number
#### String

### Any, null, undefined, unknown and never
#### any
#### null and undefined
  - optional properties (id?)
  - non-null assertion (postfix !)
#### unknown
  - Parece any, mas não permite fazer nada com o valor.
#### never

### Arrays
  - Array.isArray(...)

### enums

### BigInt

### Symbol()

### union types (t1 | t2)

### TYPE ALIAS

  - type keyword
    ```typescript
    type ID = number | string;
    ```

### INTERFACES

  - interfaces
    ```typescript
    interface Point {
      x: number;
      y: number;
    }
    ```
  - extends keyword (to extends a interface)
  - interface "expansion"
    ```typescript
    interface Window { title: string }
    interface Window { ts: TypeScriptAPI }
    ```

### Type INTERSECTIONS (&)
  - type operator &
    ```typescript
    type Animal = { name: string }
    type Bear = Animal & { honey: Boolean  }
    ```

### Type Assertions (... as XXX) ou (\<XXX\> ...)
  - literal unions 
    ```typescript
    function align(alignment: "left" | "right" | "center") { /*...*/ }
    function compare(a: string, b: string): -1 | 0 | 1 {
      return a === b ? 0 : a > b ? 1 : -1;
    }
    ```

### Functions
  > https://www.typescriptlang.org/docs/handbook/2/functions.html

#### Call Signatures
  - Call Signatures
    ```typescript
    type DescribableFunction = {
      description: string;
      (someArg: number): boolean;
    };
    function doSomething(fn: DescribableFunction) {
      console.log(fn.description + " returned " + fn(6));
    }
    ```
#### Construct Signatures
  - Construct Signatures
    ```typescript
    type SomeConstructor = {
      new (s: string): SomeObject;
    };
    function fn(ctor: SomeConstructor) {
      return new ctor("hello");
    }
    ```
#### Overload signatures
  - Overload signatures
    ```typescript
    function makeDate(timestamp: number): Date;
    function makeDate(m: number, d: number, y: number): Date;
    function makeDate(mOrTimestamp: number, d?: number, y?: number): Date {
      //...
    }
    ```
#### Generic Functions
  - Generic Functions
    ```typescript
    function firstElement<Type>(arr: Type[]): Type {
      return arr[0];
    }
    ```
#### Constraints on generics (Type extends ...)
#### Optional parameters (id?: type)
  - aceitam undefined como valor
#### Default parameters (id = 10)
  - function types are objects in TS
  - Function

### typeof function

### === operator
---

## Conceitos Importantes

### Transpiler (Compiler)

  > https://code.visualstudio.com/docs/typescript/typescript-compiling \
  > https://en.wikipedia.org/wiki/JavaScript#transpilers \
  > https://en.wikipedia.org/wiki/ECMAScript#Transpiling \
  > https://en.wikipedia.org/wiki/Source-to-source_compiler

### Declaration Files (.d.ts)

  > https://www.typescriptlang.org/docs/handbook/declaration-files/introduction.html
  - **DEFINITION**:
    - Arquivos com a extensão .d.ts que definem apenas os tipos exportados pelo módulo TS.
    - Semelhantes aos arquivos de cabeçalho (.h) em programação C/C++.
  - **EXAMPLE**:
    - https://www.typescriptlang.org/docs/handbook/declaration-files/by-example.html \
    - https://www.typescriptlang.org/docs/handbook/declaration-files/templates/module-d-ts.html

---

## Pacotes (Bibliotecas) Importantes

- DefinitelyTyped
  > https://github.com/DefinitelyTyped/DefinitelyTyped
  - **DEFINITION**:
    - Provê *high quality TypeScript type definitions*

  For an npm package "foo", typings for it will be at "@types/foo". If you can't find your package, look for it on [TypeSearch](https://www.typescriptlang.org/dt/search).

- TypeScript ESLint
  > https://github.com/typescript-eslint/typescript-eslint
  - Static code analysis of JavaScript and TypeScript projects.
    - https://github.com/typescript-eslint/tslint-to-eslint-config

- TS-Node
  > https://www.npmjs.com/package/ts-node
  - **DEFINITION**:
    - TypeScript execution and REPL for node.js


---

## Prática

### TypeScript
  - Instalar:
    > npm install typescript --save-dev
  - Inicializar
    > npx tsc --init
    Este comando cria o arquivo [tsconfig.json](./tsconfig.json).
    O arquivo [tsconfig.json](./tsconfig.json) define qual a plataforma JavaScript de destino da compilação (transpilação).
  - Compilar (Transpilar) TS para JS:
    > npx tsc

### DefinitelyTyped
  - Node TYPES
    > npm install --save-dev @types/node
     
### TypeScript ESLint
  - 
  - Instalar:
    > npm install  --save-dev
  - Inicializar
    > 
  - 


---

## Referências

    - TS Deep Dive - https://basarat.gitbook.io/typescript/
    
    - https://www.typescriptlang.org/docs/bootstrap
    
    - https://www.digitalocean.com/community/tutorials/typescript-new-project

    - https://www.typescriptlang.org/docs/handbook/
      - TypeScript Types
        - https://www.typescriptlang.org/docs/handbook/2/everyday-types.html
        - https://www.typescriptlang.org/docs/handbook/2/types-from-types.html
      - Generics
        - https://www.typescriptlang.org/docs/handbook/2/generics.html
      - OO
        - https://www.typescriptlang.org/docs/handbook/2/objects.html
        - https://www.typescriptlang.org/docs/handbook/2/classes.html
      - Modules
        - https://www.typescriptlang.org/docs/handbook/2/modules.html
      - Declaration Files
        - https://www.typescriptlang.org/docs/handbook/declaration-files/introduction.html
        - https://www.typescriptlang.org/docs/handbook/declaration-files/consumption.html
        - https://www.typescriptlang.org/docs/handbook/declaration-files/templates/module-d-ts.html