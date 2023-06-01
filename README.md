# klac
```figlet
                  _                                     __
        /\       | |                                   / _|
       /  \      | |_    __ _   ___    ___      ___   | |_
      / /\ \     | __|  / _` | / __|  / _ \    / _ \  |  _|
     / ____ \    | |_  | (_| | \__ \ |  __/   | (_) | | |
    /_/    \_\    \__|  \__,_| |___/  \___|    \___/  |_|

       _            _  _  _      _  _  _  _            _
     _(_)_       _ (_)(_)(_) _  (_)(_)(_)(_)         _(_)_
   _(_) (_)_    (_)         (_)  (_)      (_)_     _(_) (_)_
 _(_)     (_)_  (_)    _  _  _   (_)        (_)  _(_)     (_)_
(_) _  _  _ (_) (_)   (_)(_)(_)  (_)        (_) (_) _  _  _ (_)
(_)(_)(_)(_)(_) (_)         (_)  (_)       _(_) (_)(_)(_)(_)(_)
(_)         (_) (_) _  _  _ (_)  (_)_  _  (_)   (_)         (_)
(_)         (_)    (_)(_)(_)(_) (_)(_)(_)(_)    (_)         (_)
```


## how to get it
```sh
git clone -b advanced --recursive https://github.com/cmcmA20/klac
```

## if you already cloned it
```sh
git submodule update --init --recursive
```

## First step
Open any .agda file with your editor and try to typecheck it


## Setup your environment

### Using Guix

1. Install guix using your preferred method:

  - Guix System: available out of the box;
  - Arch Linux: [see arch wiki](https://wiki.archlinux.org/title/Guix);
  - Debian GNU/Linux: [guix is available since bullseye](https://packages.debian.org/bullseye/guix);
  - Ubuntu: [guix is available since impish](https://packages.ubuntu.com/jammy/guix)
  - Other distros: [Use official binary distribution](http://guix.trop.in/en/manual/devel/en/html_node/Binary-Installation.html)

2. Issue this command to launch emacs in environment:

    ```sh
    guix time-machine -C channels.scm -- shell --pure --manifest=manifest.scm -- emacs -q -l init.el
    ```


### Using GHCup

1. Install [GHCup](https://www.haskell.org/ghcup/) using official documentation.

2. Install GHC and cabal:

   ```sh
   ghcup upgrade
   ghcup install ghc 9.6.1
   ghcup set ghc 9.6.1
   ghcup install cabal 3.10.1.0
   ghcup set cabal 3.10.1.0
   cabal update
   ```

3. Install Agda 2.6.4 (master) from source, it may take a while:

   ```sh
   git clone https://github.com/agda/agda/ ~/agda
   cd ~/agda
   cabal build
   cabal install --overwrite-policy=always
   ```

4. Install fix-whitespace:

   ```sh
   cd ~
   cabal install fix-whitespace
   ```

4. Install libraries:

   mini cubical library
   ```sh
   git clone https://github.com/cmcmA20/cubical-mini ~/.agda/cubical-mini
   echo "$HOME/.agda/cubical-mini/cubical-mini.agda-lib" >> ~/.agda/libraries
   ```

5. Use emacs as your editor (commands for debian/ubuntu):

   ```sh
   sudo apt update
   sudo apt install emacs -y
   agda-mode setup
   agda-mode compile
   ```

6. If you want emacs agda2-mode to load by default when opening literate agda files, add this to emacs config:

   ```lisp
   (add-to-list 'auto-mode-alist '("\\.lagda.org\\'" . agda2-mode))
   ```

### Other methods

Contributions are welcome
