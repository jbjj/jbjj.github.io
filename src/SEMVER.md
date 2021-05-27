# SEMANTIC VERSIONNING

## 1. CRIAÇÃO DE REPOSITÓRIO

A criação do repositório foi feita seguindo os passos abaixo:

1. Criar com o comando:

   > git init

2. Adicionar arquivos de markdown:
   1. Copiar o arquivo [modeloREADME.md](./modeloREADME.md) para a raiz do projeto;
   2. Renomear de modeloREADME.md para README.md;
   3. Para projetos privados, copiar o arquivo [LICENSE.md](./LICENSE.md) que usa [*Creative Commons Attribution-NoDerivatives 4.0 International*](https://creativecommons.org/licenses/by-nd/4.0/)
   4. Copiar o arquivo [CONTRIBUTING.md](./CONTRIBUTING.md) para a raiz do projeto;
   5. Criar pasta docs e copiar os arquivos:
       - [./docs/TEAM.md](./docs/TEAM.md)
       - [./docs/README.md](./docs/README.md)
       - [./docs/DESIGN.md](./docs/DESIGN.md)
       - [./docs/REQS.md](./docs/REQS.md)
       - [./docs/TOOLS.md](./docs/TOOLS.md)

3. Verificar README.md
     - Esse arquivo possui descrição e links para:
       - ./LICENSE.md
         - Para projetos privados: [*Creative Commons Attribution-NoDerivatives 4.0 International*](https://creativecommons.org/licenses/by-nd/4.0/)
       - ./CONTRIBUTING.md
       - ./docs/TEAM.md
       - ./docs/README.md

4. Verificar ./docs/TEAM.md

5. Verificar ./docs/README.md

6. OPCIONAIS:

   1. Adicionar [manifest.json](manifest.json) para a raiz do projeto.

      Este arquivo deve conter:

      ```json
      {
        "short_name" : "...",
        "name" : "...",
        "version" : "1.0.0"
      } 
      ```


## 2. CONFIGURAÇÃO DO REPOSITÓRIO PARA *SEMANTIC VERSIONING SCHEMA* (REGRAS DE COMMIT E CHANGELOG)

A configuração do repositório para [*semantic versioning schema (major.minor.patch)*](https://semver.org/) foi feita seguindo os passos abaixo:

1. Criar o arquivo [**package.json**](./package.json):

   > npm init -y

   Que já carrega as definições do github para o arquivo [**package.json**](./package.json).

   e Modificado o arquivo [**package.json**](./package.json):
   - Adicionada descrição do repositório;
   - Adicionado autor: Joabe Jesus;
   - Modificado licença de "ISC" para "CC BY-ND 4.0" (ver [LICENSE.md](./LICENSE.md))

2. Adicionar [standard-version](https://github.com/conventional-changelog/standard-version) para gerar o **CHANGELOG** automaticamente (a partir das informações nos commits):

   > npm install standard-version --save-dev

   Adicionando assim o [standard-version](https://github.com/conventional-changelog/standard-version) na seção de *devDependencies* no  [**package.json**](./package.json) e modificando o arquivo [**package-lock.json**](./package-lock.json), no qual o standard-version é marcado com o atributo
   
   > "dev": true,

   - GERAÇÃO DE RELEASES:

     Com o pacote **standard-version** podemos usar o comando:
   
     > npm run release
   
     ao invés de utilizar o comando:
   
     > npm version

     **OBS**: em projetos SEM JavaScript, podemos usar:

     > npx standard-version

   - **PRIMEIRA** RELEASE:

     A primeira versão pode ser gerada usando o comando:

     > npm run release -- --first-release

     Ou gerar a PRIMEIRA RELEASE com o comando:

     > npx standard-version --first-release

   - **PATCHES** (PRÉ-releases):

     No caso de **pré-releases** como PATCHES, usar o comando:

     > npm run release -- --prerelease name

     onde **name** pode ser *alpha*, *beta* ou outro identificador desejado.

   - RELEASE **NOMEADAS**:

     Mais detalhes como uso do comando
   
     > npm run release -- --release-as name

     onde **name** pode ser minor, major, patch ou outro identificador desejado, inclusive combinando com a opção de pré-release, estão disponíveis no [site npm do pacote **standard-version**](https://www.npmjs.com/package/standard-version).

3. Adicionar [commitlink](https://commitlint.js.org/) com [config-conventional](https://www.npmjs.com/package/@commitlint/config-conventional) para seguir as regras do [Angular commit convention](https://github.com/angular/angular/blob/22b96b9/CONTRIBUTING.md#-commit-message-guidelines).

   > npm install @commitlint/cli @commitlint/config-conventional --save-dev

   Criando assim a seção de *devDependencies* no [**package.json**](./package.json) e o arquivo [**package-lock.json**](./package-lock.json), no qual as dependências são marcadas com o atributo
   
   > "dev": true,

   E realizada configuração do [commitlink](https://commitlint.js.org/) com a criação do arquivo [**commitlint.config.js**](./commitlint.config.js) contendo o código abaixo:

   > module.exports = {extends: ['@commitlint/config-conventional']};

   Embora esse arquivo possa ser criado com o comando abaixo: 

   > echo "module.exports = {extends: ['@commitlint/config-conventional']};" > commitlint.config.js

   Alguns erros de encoding podem acontecer, como o discutido na [issue 614 do commitlint](https://github.com/conventional-changelog/commitlint/issues/614).

   Para teste do funcionamento do commitlint pode ser usado o exemplo a seguir:

   > echo 'feat: Adicionada funcionalidade XPTO' | npx commitlint

4. Adicionar [husky](https://github.com/typicode/husky) para ativar os *Git hooks*:

   > npm install husky --save-dev

   Adicionando assim o [husky](https://github.com/typicode/husky) na seção de *devDependencies* no  [**package.json**](./package.json) e modificando o arquivo [**package-lock.json**](./package-lock.json), no qual o husky é marcado com o atributo
   
   > "dev": true,

   Também foi criada pasta [**./.husky/**](./.husky/) com o comando:

   > npx husky install

   Essa pasta armazena os *Git hooks* e o script [**./.husky/_/husky.sh**](./.husky/_/husky.sh). Além disso, o comando adiciona o arquivo [**./.husky/.gitignore**](./.husky/.gitignore) que lista a pasta [**./.husky/_**](./.husky/_/) como ignorada.

5. Configurar os *Git hooks* de **pre-commit** e **commit-msg**:

   - Criado arquivo [**./.husky/pre-commit**](./.husky/pre-commit) com o comando:

     > npx husky-init

     Esse comando ativa o *Git hook* de pré-commit (com os comandos listados no arquivo [**./.husky/pre-commit**](./.husky/pre-commit)).

   - Criado arquivo [**./.husky/commit-msg**](./.husky/commit-msg) com o commando:

     > npx husky add .husky/commit-msg

     Esse arquivo contém o código a seguir:

     ```sh
     #!/bin/sh
     . "$(dirname "$0")/_/husky.sh"
     
     undefined
     ```

     Esse código está baseado no conteúdo do arquivo [**./.husky/pre-commit**](./.husky/pre-commit) e na descrição de [*migração da versão 4 para a versão 6 do husky*](https://github.com/typicode/husky/blob/main/docs/README.md#migrate-from-v4-to-v6).

     Esse arquivo ativa o *Git hook* de commit-msg (com os comandos listados no arquivo [**./.husky/commit-msg**](./.husky/commit-msg)). Assim, ativa-se o uso do commitlint quando for realizado um comando **git commit**.

     Assim, foi modificado o arquivo [**./.husky/commit-msg**](./.husky/commit-msg) para conter o comando:

     > npx --no-install commitlint --edit $1

     Que realiza o lint da mensagem de commit.

6. Adicionar [commitzen](https://github.com/commitzen/cz-cli) para seguir as regras de commit de com um wizard:

   > npm install commitizen --save-dev

   E inicializar o cz com o comando:

   > npx commitizen init cz-conventional-changelog --save-dev --save-exact

   Adicionando assim o [husky](https://github.com/commitzen/cz-conventional-changelog) na seção de *devDependencies* no  [**package.json**](./package.json) e modificando o arquivo [**package-lock.json**](./package-lock.json), no qual o cz-conventional-changelog é marcado com o atributo
   
   > "dev": true,


## Referências

- https://git-scm.com/docs/git-init
- https://guides.github.com/features/mastering-markdown/
- https://www.w3.org/TR/appmanifest/

- https://creativecommons.org/licenses/by-nd/4.0/

- https://docs.npmjs.com/cli
- https://docs.npmjs.com/cli/v7/using-npm/scripts

- Badges
  - https://shields.io
  - https://github.com/badges/shields
    - https://shields.io/category/version
      - https://github.com/badges/shields/issues/593

- Dependências
  - https://docs.npmjs.com/cli/v7/commands/npm-update

- Semantic Versioning
  - https://semver.org/

  - https://github.com/conventional-changelog/standard-version
    - https://www.npmjs.com/package/standard-version

  - https://github.com/conventional-changelog/commitlint
    - https://commitlint.js.org/
    - https://www.npmjs.com/package/@commitlint/config-conventional
  - https://github.com/typicode/husky/
  - https://github.com/commitizen/cz-cli

  - Angular commit convention
    - https://github.com/angular/angular/blob/22b96b9/CONTRIBUTING.md#-commit-message-guidelines
  - https://github.com/conventional-changelog/commitlint/issues/614
  - https://github.com/typicode/husky/blob/main/docs/README.md#migrate-from-v4-to-v6
  - https://blog.typicode.com/husky-git-hooks-javascript-config/
  - https://www.mokkapps.de/blog/how-to-automatically-generate-a-helpful-changelog-from-your-git-commit-messages/
  - https://medium.com/@klauskpm/how-to-create-good-commit-messages-67943d30cced

