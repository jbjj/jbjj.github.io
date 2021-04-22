# JavaScript

  > https://tc39.es/
    
    Ecma International's TC39 is a group of JavaScript developers, implementers, academics, and more, collaborating with the community to maintain and evolve the definition of JavaScript.

## ECMAScript
   > https://tc39.es/ecma262/

   - A general-purpose programming language, standardised by Ecma International according to the document [ECMA-262](https://www.ecma-international.org/publications/standards/Ecma-262.htm).

   - ECMA-262 or the ECMAScript Language Specification defines the ECMAScript Language, or just ECMAScript (aka JavaScript)

---

## Linguagem

### 1. Arrow functions
  - Introduzido na 6a Edição (ECMAScript 2015)
  - **EXAMPLE**:
    ```javascript
    const short_example = (input1, input2) => input1 + input2;
    short_example(2, 5);  // Returns 7
    ```

### 2. Function closures
  > https://en.wikipedia.org/wiki/JavaScript#Uses_outside_Web_pages
  - **DEFINITION**:
    - Permite capturar as variáveis não-locais por referência.
  - **EXAMPLE**:
    ```javascript
    function counter() {
        let count = 0;

        return function() {
            return ++count;
        };
    }

    let closure = counter();
    closure(); // returns 1
    closure(); // returns 2
    closure(); // returns 3
    ```
    counter functions works as an object.

### 3. Variadic function
  - **DEFINITION**:
    - Permite declarar função sem parâmetros e passar diversos
    - Possui uma variável especial chamada *arguments*
  - **EXAMPLE**:
    ```javascript
    function sum() {
        let x = 0;

        for (let i = 0; i < arguments.length; ++i)
            x += arguments[i];

        return x;
    }

    sum(1, 2); // returns 3
    sum(1, 2, 3); // returns 6
    ```


---

## Linguagens RELACIONADAS

   > ver [TYPEScript](./TS.md).

   > ver [NATIVEScript](./NATIVEJS.md).

   > ver [Ruby](./RUBY.md).


---

## Conceitos Importantes

### POLYFILLs
  > https://developer.mozilla.org/en-US/docs/Glossary/Polyfill \
  > https://remysharp.com/2010/10/08/what-is-a-polyfill
  - **DEFINITION**:
    - A polyfill is a piece of code (usually JavaScript on the Web) used to provide modern functionality on older browsers that do not natively support it.
  - **BENEFITS**:
    - Fill the browser gap.
  - **EXAMPLE**:
    - The 1st version of [JQuery](https://ajax.googleapis.com/ajax/libs/jquery/1.12.4/jquery.js) was an early example of a polyfill. It was essentially a compilation of browser-specific workarounds to provide JavaScript developers with a single common API that worked in all browsers.
  - **PROBLEMS**:
    - Performance
    - 

### MODULES - CommonJS API

- CommonJS (Aug,2009) / ServerJS (Jan,2009)
  > http://www.commonjs.org \
  > https://en.wikipedia.org/wiki/CommonJS \
  > https://medium.com/@cgcrutch18/commonjs-what-why-and-how-64ed9f31aa46#:~:text=CommonJS%20is%20a%20module%20formatting,heavily%20influenced%20NodeJS's%20module%20management
  - **DEFINITION**:
    - A module formatting system. A standard for structuring and organizing JavaScript code.
  - **BENEFITS**:
    - Establish conventions on the module ecosystem for JavaScript outside of the web browser.
    - Assists in the server-side development of apps and it’s format has heavily influenced NodeJS’s module management.
    - With CommonJS-compliant systems, you can use JavaScript to write:
      - Server-side JavaScript applications
      - Command line tools
      - Desktop GUI-based applications
      - Hybrid applications (Titanium, Adobe AIR)
  - **EXAMPLE**:
    ```javascript
    const maxInterval = 12;
    function getArrayLength(arr) {
    return arr.length;
    }
    module.exports = {
        getArrayLength,
        maxInterval,
    };
    ```
  - **PROBLEMS**:
    - .


### DEPENDENCIES

  Pacotes JS são publicados (no NPM) com uma [Semantic Version (major.minor.patch)](https://semver.org).
  > Mais informções em: https://docs.npmjs.com/about-semantic-versioning

  Assim, as dependências em JS podem ser de uma versão específica (major.minor.patch), Caret (^) ou Tilde (~).
  > Mais informções em: https://docs.npmjs.com/cli/v7/commands/npm-update.

- Dependências Globais

  Instaladas na máquina e NÃO conhecidas pelo projeto (package.json).

- Dependências Locais

  Instaladas no projeto (node_modules) e SÂO conhecidas pelo projeto (package.json).

  - Dependências de desenvolvimento
    > npm install --save-dev ...

  - Dependências do sistema
    > npm install --save ...


### PACKAGE MANAGERS - NPM e YARN

    Gerenciador de pacotes (bibliotecas) JavaScript / TypeScript.

- NPM - Node package manager
  > http://www.npmjs.com
  - **EXAMPLE**:
    > npm install -g typescript

- Yarn
  > https://yarnpkg.com/
  - **EXAMPLE**:
    > yarn add typescript

### RUNTIME - Node.JS

- Node.JS
  > http://www.nodejs.org
  - **DEFINITION**:
    - A JavaScript runtime built on [Chrome's V8 JavaScript engine](https://v8.dev/).
  - **BENEFITS**:
    - Asynchronous event-driven JS runtime, designed to build scalable network applications.
      - https://nodejs.org/en/docs/guides/blocking-vs-non-blocking/
  - **EXAMPLE**:
    - .

### COMPILERS

- Babel
  > https://babeljs.io/
  - **DEFINITION**:
    - JavaScript compiler.
  - **BENEFITS**:
    - Get browser-compatible JavaScript out.


### LINTERS (static analysers)

- ESLint
  > https://eslint.org/
  - **DEFINITION**:
    - ECMAScript/JavaScript Linter
  - **BENEFITS**:
    - .

- Futures and promises
  > https://en.wikipedia.org/wiki/Futures_and_promises

---

## Pacotes/Bibliotecas Importantes

- Prototype.js (Feb,2005)
  > https://en.wikipedia.org/wiki/Prototype_JavaScript_Framework
  - **BENEFITS**:
    - $(), $F() and $$() functions
    - OO: Ajax object, Class.create and Object.extend functions
  - **PROBLEMS**:
    - Prototype extends the DOM. So, ...

- JQuery (Aug,2006)
  > https://jquery.com/
  - **BENEFITS**:
    - Designed to simplify HTML DOM tree traversal and manipulation
    - event handling, CSS animation
    - start-point: $(handler)
      - jQuery object
      - JQuery Selector ($(...) == document.getElements(...))
    - $.noConflict() function
    - Chaining
    - Ajax - $.ajax()
      - .then() and .catch() callbacks

- MooTools (Mar,2007)
  > https://mootools.net/ \
  > https://github.com/mootools/mootools-core
  - **BENEFITS**:
    - An extensible and modular framework allowing developers to choose their own customized combination of components. https://en.wikipedia.org/wiki/MooTools
    - OO, Ajax, Event handlers
    - MooTools Selectors ($$(...) == document.getElements(...))
  - **PROBLEMS**:
    - .

- Lodash (Apr,2012)
  > https://lodash.com/ \
  > https://github.com/lodash/lodash/wiki/FP-Guide
  - **BENEFITS**:
    - Makes JS easier by taking the hassle out of working with arrays, numbers, objects, strings, etc.
    - O objeto _
    - [LODASH FP](https://github.com/lodash/lodash/wiki/FP-Guide)
  - **EXAMPLE**:
    - .
  - **PROBLEMS**:
    - .

- n_
  > https://www.npmjs.com/package/n_
  - **DEFINITION**:
    - Node.JS REPL (Read-Eval-Print Loop) com suporte a LODASH.
  - **BENEFITS**:
    - Permite usar o lodash no Node REPL.

- Underscore.js (Oct,2009)
  > http://underscorejs.org/ \
  > https://github.com/jashkenas/underscore \
  > https://en.wikipedia.org/wiki/Underscore.js
  - **DEFINITION**:
    - provides a whole mess of useful functional programming helpers without extending any built-in objects.
  - **BENEFITS**:
    - provides over 100 functions that support both your favorite workaday functional helpers: map, filter, invoke — as well as more specialized goodies: function binding, javascript templating, creating quick indexes, deep equality testing, and so on.

- Backbone.js (Oct,2010)
  > https://backbonejs.org/ \
  > https://github.com/jashkenas/backbone \
  > https://github.com/jashkenas/backbone/wiki
  - **DEFINITION**:
    - gives structure to web applications by providing models with key-value binding and custom events, collections with a rich API of enumerable functions, views with declarative event handling, and connects it all to your existing API over a RESTful JSON interface.
  - **DEPENDS ON**:
    - Underscore.js
  - **BENEFITS**:
    - .

- JQuery Mobile
  > https://jquerymobile.com/ \
  > https://en.wikipedia.org/wiki/JQuery_Mobile

- Require.JS
  > https://requirejs.org/docs/commonjs.html
  - **DEFINITION**:
    - .
  - **BENEFITS**:
    - .

- Angular
  > ver o [./ANGULAR.md](./kb/ANGULAR.md)

- Bootstrap
  > ver o [./BOOTSTRAP.md](./kb/BOOTSTRAP.md)

- URL handling
  > https://developer.mozilla.org/en-US/docs/Web/API/URL/URL


---

## Prática

### NPM

### Node.JS

### ESLint

  - 
