# JEKYLL

  > https://jekyllrb.com

    Jekyll is a static site generator.

---

## JEKYLL is a Ruby gem.

---

## Conceitos Importantes

- Ruby GEMS
  > https://jekyllrb.com/docs/ruby-101/#gems \
  > Ver [Ruby GEMS](./RUBY.md)
  - Jekyll is a gem. Many Jekyll plugins are also gems...

- Gemfile
  > https://jekyllrb.com/docs/ruby-101/#gems \
  > Ver [Ruby GEMS](./RUBY.md)
  - Every Jekyll site has a **Gemfile** in the main folder.
  - **Example**:
    ```ruby
    source "https://rubygems.org"

    gem "jekyll"

    group :jekyll_plugins do
    gem "jekyll-feed"
    gem "jekyll-seo-tag"
    end
    ```

- Liquid templating language
  > https://shopify.github.io/liquid \
  > https://github.com/Shopify/liquid \
  > https://jekyllrb.com/docs/liquid

---

## Referências

- https://jekyllrb.com/docs/
- https://jekyllrb.com/docs/usage/
- https://jekyllrb.com/docs/liquid/