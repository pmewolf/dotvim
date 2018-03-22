if has("win16") || has("win32") || has("win64")
    "let $dotvim="$VIM/../../Data/settings/dotvim"
    let $dotvim="C:/Users/xuhu-local/dotvim"
else
    let $dotvim="~/dotvim"
endif


"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" Vundle
set nocompatible              " be iMproved, required
filetype off                  " required

" set the runtime path to include Vundle and initialize
set rtp+=$dotvim/bundle/Vundle.vim
let $vundle_path='$dotvim/bundle'
call vundle#begin($vundle_path)
" alternatively, pass a path where Vundle should install plugins
"call vundle#begin('~/some/path/here')

" let Vundle manage Vundle, required
Plugin 'VundleVim/Vundle.vim'

source $dotvim/plugin_list.vim

" All of your Plugins must be added before the following line
call vundle#end()            " required
filetype plugin indent on    " required
" To ignore plugin indent changes, instead use:
"filetype plugin on
"
" Brief help
" :PluginList       - lists configured plugins
" :PluginInstall    - installs plugins; append `!` to update or just :PluginUpdate
" :PluginSearch foo - searches for foo; append `!` to refresh local cache
" :PluginClean      - confirms removal of unused plugins; append `!` to auto-approve removal
"
" see :h vundle for more details or wiki for FAQ
" Put your non-Plugin stuff after this line

"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" Amix's setting
"set runtimepath+=~/.vim_runtime
"source $dotvim/vimrcs/basic.vim
"source $dotvim/vimrcs/filetypes.vim
"source $dotvim/vimrcs/plugins_config.vim
"source $dotvim/vimrcs/extended.vim

"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" My setting
source $dotvim/my_vimrc.vim
