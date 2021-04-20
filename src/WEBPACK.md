# Empacotamento

- WEBPACK
  > https://webpack.js.org/guides/getting-started \
  > https://webpack.js.org/configuration/mode \
  > https://www.npmjs.com/package/webpack

     > npm install webpack webpack-cli --save-dev
   
     > npx webpack --mode=development

     ou

     > npx webpack --mode=production

     Caso seja adicionado uma propriedade chamada *build* à seção *script* do **package.json**, como abaixo:
     
     > "scripts": {
     >   "build": "webpack",
     
     podemos usar, ao invés do npx, o comando abaixo:

     > npm run build -- --mode=development

     Assim evita-se rodar uma cópia local do webpack a partir do CLI.
