# RUBY

  > https://www.ruby-lang.org

    A dynamic, open source programming language with a focus on simplicity and productivity.

---

## Conceitos Importantes

- Ruby SDK
  > https://rubyinstaller.org/

- Ruby Bibliography
  > https://rubybib.org/
  - Academic writing on the Ruby programming language

- Ruby GEM
  > https://guides.rubygems.org/what-is-a-gem/
  - A GEM has:
    - Code (including tests and supporting utilities)
    - Documentation
    - Arquivo meuGem.gemspec
  - A gem *usually* has a Rakefile

- Gemfile
  > https://bundler.io/gemfile.html
  - Gemfiles require at least one gem source, in the form of the URL for a RubyGems server.
  - Most of the version specifiers, like >= 1.0, are self-explanatory. The specifier ~> has a special meaning, best shown by example. ~> 2.0.3 is identical to >= 2.0.3 and < 2.1. ~> 2.1 is identical to >= 2.1 and < 3.0. ~> 2.2.beta will match prerelease versions like 2.2.beta.12. ~> 0 is identical to >= 0.0 and < 1.0.
  - **Exampple**:

        source 'https://rubygems.org'

        gem 'nokogiri'
        gem 'rails', '5.0.0'
        gem 'rack',  '>=1.0'
        gem 'thin',  '~>1.1'

        source 'https://gems.example.com' do
            # Gems from the alternative source here
        end

- Rakefile (Ruby mAKEfile)
  > https://rubygems.org/gems/rake

- RAKE (Ruby mAKE)
  > https://ruby.github.io/rake \
  > https://rubygems.org/gems/rake
  - Rake is a Make-like program implemented in Ruby
  - **Example**:

        task default: %w[test]

        task :test do
            ruby "test/unittest.rb"
        end

    In this example, the default task needs the test task. Calling rake without arguments will execute the default task.

- Bundler
  > https://bundler.io \
  > https://rubygems.org/gems/bundler
  - Bundler manages an application's dependencies through its entire life, across many machines, systematically and repeatably

- RubyGems
  > https://rubygems.org
  - RubyGems is a package management framework for Ruby
  
  - Instalação com o comando GEM (instalado com o SDK do Ruby):
    > gem update --system

  - Instalação manual:
    1. Fazer download do arquivo .zip no link: https://rubygems.org/pages/download;
    2. Descompactar o arquivo numa nova pasta adequada;
    3. Ir para a pasta adequada;
    4. Executar o comando:
       > ruby setup.rb
    5. Para AJUDA, usar o comando:
       > ruby setup.rb --help

- Documentação
  - RDoc
    > http://rdoc.sourceforge.net/doc
  - YARD
    > https://yardoc.org/
