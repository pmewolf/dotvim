" ---------------------------------------------------------
"   my_vimrc.vim
"       https://github.com/pmewolf/dotvim
"
"   Contents
"       S1 Basic
"           S1a General
"           S1b VIM user interface
"           S1c Colors, Fonts and GUI
"           S1d Files, backups and undo
"           S1e Text, tab and indent related
"           S1f Visual mode related
"           S1g Moving around, tabs, windows and buffers
"           S1h Status line
"           S1i Editing mappings
"           S1j Spell checking
"           S1k Misc
"           S1l Helper functions
"       S2 FileTypes
"           S2a Python section
"           S2b JavaScript section
"           S2c CoffeeScript section
"           S2d Shell section
"           S2e Twig section
"           S2f Verilog/SystemVerilog section
"       S3 Extended
"           S3a GUI related
"           S3b Fast editing and reloading of vimrc configs
"           S3c Turn persistent undo on
"           S3d Command mode related
"           S3e Parenthesis/bracket
"           S3f General abbreviations
"           S3g Omni complete functions
"           S3h Ack searching and cope displaying
"           S3i Helper functions
"       S5 Self Setting
"           S5a File I/O
"           S5b Search and replace
"           S5c Display and GUI
"           S5d Other
"       S8 Some Note
"       S9 SandBox
" ---------------------------------------------------------


" ---------------------------
"   S1 Basic
" ---------------------------
if has("win16") || has("win32")
    behave mswin
    let $dotvim="$VIM/../../Data/settings/dotvim"
else
    let $dotvim="~/dotvim"
endif

behave xterm
"behave mswin

" ---------------------------
"   S1a General
" ---------------------------
" Sets how many lines of history VIM has to remember
set history=500

" Enable filetype plugins
filetype plugin on
filetype indent on

" Set to auto read when a file is changed from the outside
set autoread        

" Change leader key
let mapleader = ","
let g:mapleader = ","

" Fast saving
nmap <leader>w :w!<cr>

" :W sudo saves the file (useful for handling the permission-denied error)
command! W w !sudo tee % > /dev/null

" ---------------------------
"   S1b VIM user interface
" ---------------------------
" Set 7 lines to the cursor - when moving vertically using j/k
set so=7

" Avoid garbled characters in Chinese language windows OS
let $LANG='en' 
set langmenu=en
source $VIMRUNTIME/delmenu.vim
source $VIMRUNTIME/menu.vim

" Turn on the WiLd menu
set wildmenu

" Ignore compiled files
set wildignore=*.o,*~,*.pyc
if has("win16") || has("win32")
    set wildignore+=.git\*,.hg\*,.svn\*
else
    set wildignore+=*/.git/*,*/.hg/*,*/.svn/*,*/.DS_Store
endif

"Always show current position
set ruler

" Height of the command bar
set cmdheight=2

" A buffer becomes hidden when it is abandoned
set hid

" Configure backspace so it acts as it should act
set backspace=eol,start,indent
set whichwrap+=<,>,h,l

" Ignore case when searching
set ignorecase

" When searching try to be smart about cases 
set smartcase

" Highlight search results
set hlsearch

" Makes search act like search in modern browsers
set incsearch 

" Don't redraw while executing macros (good performance config)
set lazyredraw 

" For regular expressions turn magic on
set magic

" Show matching brackets when text indicator is over them
set showmatch 
" How many tenths of a second to blink when matching brackets
set mat=2

" No annoying sound on errors
set noerrorbells
set novisualbell
set t_vb=
set tm=500

" Properly disable sound on errors on MacVim
if has("gui_macvim")
    autocmd GUIEnter * set vb t_vb=
endif

" Add a bit extra margin to the left
set foldcolumn=1

" ---------------------------
"   S1c Colors, Fonts and GUI
" ---------------------------
" Enable syntax highlighting
syntax enable 

" Enable 256 colors palette in Gnome Terminal
if $COLORTERM == 'gnome-terminal'
    set t_Co=256
endif

try
    colorscheme peaksea
    "colorscheme ir_black
    "colorscheme desert
catch
endtry

set background=dark

" Set extra options when running in GUI mode
if has("gui_running")
    set guioptions-=T
    set guioptions-=e
    set t_Co=256
    set guitablabel=%M\ %t
endif

" Set utf8 as standard encoding and en_US as the standard language
set encoding=utf8

" Use Unix as the standard file type
set ffs=unix,dos,mac

" ---------------------------
"   S1d Files, backups and undo
" ---------------------------
" Turn backup off, since most stuff is in SVN, git et.c anyway...
set nobackup
"set backup
set nowb
set noswapfile

try
if has("win16") || has("win32")
    set backupdir=$VIM/../../Data/settings/dotvim/temp_dirs/back,.
    set directory=$VIM/../../Data/settings/dotvim/temp_dirs/swp,.
else
    set backupdir=~/dotvim/temp_dirs/back,.
    set directory=~/dotvim/temp_dirs/swp,.
endif
catch
endtry

" ---------------------------
"   S1e Text, tab and indent related 
" ---------------------------
" Use spaces instead of tabs
set expandtab

" Be smart when using tabs ;)
set smarttab

" 1 tab == 4 spaces
set shiftwidth=4
set tabstop=4

" Linebreak on 500 characters
set lbr
set tw=500

set ai "Auto indent
set si "Smart indent
"set wrap "Wrap lines
set nowrap

" ---------------------------
"   S1f Visual mode related 
" ---------------------------
" Visual mode pressing * or # searches for the current selection
" Super useful! From an idea by Michael Naumann
vnoremap <silent> * :<C-u>call VisualSelection('', '')<CR>/<C-R>=@/<CR><CR>
vnoremap <silent> # :<C-u>call VisualSelection('', '')<CR>?<C-R>=@/<CR><CR>

" ---------------------------
"   S1g Moving around, tabs, windows and buffers
" ---------------------------
" Map <Space> to / (search) and Ctrl-<Space> to ? (backwards search)
map <space> /
map <c-space> ?

" Disable highlight when <leader><cr> is pressed
map <silent> <leader><cr> :noh<cr>

" Smart way to move between windows
map <C-j> <C-W>j
map <C-k> <C-W>k
map <C-h> <C-W>h
map <C-l> <C-W>l

" Close the current buffer
map <leader>bd :Bclose<cr>:tabclose<cr>gT

" Close all the buffers
map <leader>ba :bufdo bd<cr>

map <leader>l :bnext<cr>
map <leader>h :bprevious<cr>

" Useful mappings for managing tabs
map <leader>tn :tabnew<cr>
map <leader>to :tabonly<cr>
map <leader>tc :tabclose<cr>
map <leader>tm :tabmove 
map <leader>t<leader> :tabnext 

"map <C-i> :tabNext<cr>
"map <C-o> :tabnext<cr>
"map <C-o> :tabNext<cr>
"map <C-p> :tabnext<cr>

" Let 'tl' toggle between this and the last accessed tab
let g:lasttab = 1
nmap <Leader>tl :exe "tabn ".g:lasttab<CR>
au TabLeave * let g:lasttab = tabpagenr()

" Opens a new tab with the current buffer's path
" Super useful when editing files in the same directory
map <leader>te :tabedit <c-r>=expand("%:p:h")<cr>/

" Switch CWD to the directory of the open buffer
map <leader>cd :cd %:p:h<cr>:pwd<cr>

" Specify the behavior when switching between buffers 
try
  set switchbuf=useopen,usetab,newtab
  set stal=2
catch
endtry

" Return to last edit position when opening files (You want this!)
au BufReadPost * if line("'\"") > 1 && line("'\"") <= line("$") | exe "normal! g'\"" | endif

" ---------------------------
"   S1h Status line
" ---------------------------
" Always show the status line
set laststatus=2

" Format the status line
"set statusline=\ %{HasPaste()}%F%m%r%h\ %w\ \ CWD:\ %r%{getcwd()}%h\ \ \ Line:\ %l\ \ Column:\ %c
set statusline=\ %{HasPaste()}%F%m%r%h\ %w\ \ CWD:\ %r%{getcwd()}%h\ \ \ Line:\ %l,%v,%p%%

" ---------------------------
"   S1i Editing mappings 
" ---------------------------
" Remap VIM 0 to first non-blank character
map 0 ^

" Move a line of text using ALT+[jk] or Command+[jk] on mac
nmap <M-j> mz:m+<cr>`z
nmap <M-k> mz:m-2<cr>`z
vmap <M-j> :m'>+<cr>`<my`>mzgv`yo`z
vmap <M-k> :m'<-2<cr>`>my`<mzgv`yo`z
"nmap <S-j> mz:m+<cr>`z
"nmap <S-k> mz:m-2<cr>`z
vmap <S-j> :m'>+<cr>`<my`>mzgv`yo`z
vmap <S-k> :m'<-2<cr>`>my`<mzgv`yo`z

if has("mac") || has("macunix")
  nmap <D-j> <M-j>
  nmap <D-k> <M-k>
  vmap <D-j> <M-j>
  vmap <D-k> <M-k>
endif

" Delete trailing white space on save, useful for some filetypes ;)
fun! CleanExtraSpaces()
    let save_cursor = getpos(".")
    let old_query = getreg('/')
    silent! %s/\s\+$//e
    call setpos('.', save_cursor)
    call setreg('/', old_query)
endfun

if has("autocmd")
    autocmd BufWritePre *.txt,*.js,*.py,*.wiki,*.sh,*.coffee :call CleanExtraSpaces()
endif

" ---------------------------
"   S1j Spell checking
" ---------------------------
" Pressing ,ss will toggle and untoggle spell checking
map <leader>ss :setlocal spell!<cr>

" Shortcuts using <leader>
map <leader>sn ]s
map <leader>sp [s
map <leader>sa zg
map <leader>s? z=

" ---------------------------
"   S1k Misc
" ---------------------------
" Remove the Windows ^M - when the encodings gets messed up
noremap <Leader>m mmHmt:%s/<C-V><cr>//ge<cr>'tzt'm

" Quickly open a buffer for scribble
map <leader>q :e ~/buffer<cr>

" Quickly open a markdown buffer for scribble
map <leader>x :e ~/buffer.md<cr>

" Toggle paste mode on and off
map <leader>pp :setlocal paste!<cr>

" ---------------------------
"   S1l Helper functions
" ---------------------------
" Returns true if paste mode is enabled
function! HasPaste()
    if &paste
        return 'PASTE MODE  '
    endif
    return ''
endfunction

" Don't close window, when deleting a buffer
command! Bclose call <SID>BufcloseCloseIt()
function! <SID>BufcloseCloseIt()
   let l:currentBufNum = bufnr("%")
   let l:alternateBufNum = bufnr("#")

   if buflisted(l:alternateBufNum)
     buffer #
   else
     bnext
   endif

   if bufnr("%") == l:currentBufNum
     new
   endif

   if buflisted(l:currentBufNum)
     execute("bdelete! ".l:currentBufNum)
   endif
endfunction

function! CmdLine(str)
    exe "menu Foo.Bar :" . a:str
    emenu Foo.Bar
    unmenu Foo
endfunction 

function! VisualSelection(direction, extra_filter) range
    let l:saved_reg = @"
    execute "normal! vgvy"

    let l:pattern = escape(@", "\\/.*'$^~[]")
    let l:pattern = substitute(l:pattern, "\n$", "", "")

    if a:direction == 'gv'
        call CmdLine("Ack '" . l:pattern . "' " )
    elseif a:direction == 'replace'
        call CmdLine("%s" . '/'. l:pattern . '/')
    endif

    let @/ = l:pattern
    let @" = l:saved_reg
endfunction

" ---------------------------
"   S2 FileTypes
" ---------------------------

" ---------------------------
"   S2a Python section
" ---------------------------
let python_highlight_all = 1
au FileType python syn keyword pythonDecorator True None False self

au BufNewFile,BufRead *.jinja set syntax=htmljinja
au BufNewFile,BufRead *.mako set ft=mako

au FileType python map <buffer> F :set foldmethod=indent<cr>

au FileType python inoremap <buffer> $r return 
au FileType python inoremap <buffer> $i import 
au FileType python inoremap <buffer> $p print 
au FileType python inoremap <buffer> $f # --- <esc>a
au FileType python map <buffer> <leader>1 /class 
au FileType python map <buffer> <leader>2 /def 
au FileType python map <buffer> <leader>C ?class 
au FileType python map <buffer> <leader>D ?def 
au FileType python set cindent
au FileType python set cinkeys-=0#
au FileType python set indentkeys-=0#

set filetype=python
au BufNewFile,BufRead *.py,*.pyw setf python

"nmap <F5>  :! ..\Python3251\App\python.exe %<CR>
"au BufReadPost *.py nmap <F5> :w<CR> :! ..\Python3251\App\python.exe %<CR>
"au FileType python nmap <F5> :! ..\Python3251\App\python.exe %<CR>
"au FileType python nmap <F5> :! ..\..\..\PortableApps\Python3251\App\python.exe %<CR>
if $VIM == 'C:\Users\alfie.huang\OneDrive\Personal\Portable\PortableApps\gVimPortable\App\vim'
    "au FileType python nmap <F5> :! C:\Users\alfie.huang\OneDrive\Personal\Portable\PortableApps\Python2761\App\python.exe %
    au FileType python nmap <F5> :! C:\Users\alfie.huang\OneDrive\Personal\Portable\PortableApps\Python3251\App\python.exe %
else 
    au FileType python nmap <F5> :! python3.3 %<CR>
endif

" ---------------------------
"   S2b JavaScript section
" ---------------------------
au FileType javascript call JavaScriptFold()
au FileType javascript setl fen
au FileType javascript setl nocindent

au FileType javascript imap <c-t> $log();<esc>hi
au FileType javascript imap <c-a> alert();<esc>hi

au FileType javascript inoremap <buffer> $r return 
au FileType javascript inoremap <buffer> $f // --- PH<esc>FP2xi

function! JavaScriptFold() 
    setl foldmethod=syntax
    setl foldlevelstart=1
    syn region foldBraces start=/{/ end=/}/ transparent fold keepend extend

    function! FoldText()
        return substitute(getline(v:foldstart), '{.*', '{...}', '')
    endfunction
    setl foldtext=FoldText()
endfunction

" ---------------------------
"   S2c CoffeeScript section
" ---------------------------
function! CoffeeScriptFold()
    setl foldmethod=indent
    setl foldlevelstart=1
endfunction
au FileType coffee call CoffeeScriptFold()

au FileType gitcommit call setpos('.', [0, 1, 1, 0])

" ---------------------------
"   S2d Shell section
" ---------------------------
if exists('$TMUX') 
    if has('nvim')
        set termguicolors
    else
        set term=screen-256color 
    endif
endif

" ---------------------------
"   S2e Twig section 
" ---------------------------
autocmd BufRead *.twig set syntax=html filetype=html

" ---------------------------
"   S2f Verilog/SystemVerilog section
" ---------------------------
" Parenthesis/bracket
inoremap $B begin<esc>oend<esc>O

" ---------------------------
"   S3 Extended
" ---------------------------

" ---------------------------
"   S3a GUI related
" ---------------------------
" Set font according to system
if has("mac") || has("macunix")
    set gfn=Menlo:h15
    "set gfn=IBM\ Plex\ Mono:h14,Hack:h14,Source\ Code\ Pro:h15,Menlo:h15
elseif has("win16") || has("win32")
    set gfn=Consolas:h12:cANSI
    "set gfn=Courier:h14:cANSI
    "set gfn=IBM\ Plex\ Mono:h14,Source\ Code\ Pro:h12,Bitstream\ Vera\ Sans\ Mono:h11
elseif has("gui_gtk2")
    "set gfn=IBM\ Plex\ Mono:h14,:Hack\ 14,Source\ Code\ Pro\ 12,Bitstream\ Vera\ Sans\ Mono\ 11
    set gfn=Monospace\ 12
elseif has("linux")
    "set gfn=IBM\ Plex\ Mono:h14,:Hack\ 14,Source\ Code\ Pro\ 12,Bitstream\ Vera\ Sans\ Mono\ 11
    set gfn=Monospace\ 12
elseif has("unix")
    set gfn=Monospace\ 11
    "set gfn=inconsolata\ 12
    "set gfn=DejaVu\ Sans\ Mono\ 12
endif

" Disable scrollbars (real hackers don't use scrollbars for navigation!)
set guioptions-=r
set guioptions-=R
set guioptions-=l
set guioptions-=L


" ---------------------------
"   S3b Fast editing and reloading of vimrc configs
" ---------------------------
map <leader>e :e! ~/.vim_runtime/my_configs.vim<cr>
autocmd! bufwritepost ~/.vim_runtime/my_configs.vim source ~/.vim_runtime/my_configs.vim

" ---------------------------
"   S3c Turn persistent undo on
"     means that you can undo even when you close a buffer/VIM
" ---------------------------
set undofile

try
if has("win16") || has("win32")
    set undodir=$VIM/../../Data/settings/dotvim/temp_dirs/undodir
else
    set undodir=~/dotvim/temp_dirs/undodir
endif
catch
endtry

" ---------------------------
"   S3d Command mode related
" ---------------------------
" Smart mappings on the command line
cno $h e ~/
"cno $d e ~/Desktop/
cno $j e ./
cno $c e <C-\>eCurrentFileDir("e")<cr>

" $q is super useful when browsing on the command line
" it deletes everything until the last slash 
cno $q <C-\>eDeleteTillSlash()<cr>

" Bash like keys for the command line
cnoremap <C-A>		<Home>
cnoremap <C-E>		<End>
cnoremap <C-K>		<C-U>

cnoremap <C-P> <Up>
cnoremap <C-N> <Down>

" Map ½ to something useful
map ½ $
cmap ½ $
imap ½ $

" ---------------------------
"   S3e Parenthesis/bracket
" ---------------------------
vnoremap $1 <esc>`>a)<esc>`<i(<esc>
vnoremap $2 <esc>`>a]<esc>`<i[<esc>
vnoremap $3 <esc>`>a}<esc>`<i{<esc>
vnoremap $$ <esc>`>a"<esc>`<i"<esc>
vnoremap $q <esc>`>a'<esc>`<i'<esc>
vnoremap $e <esc>`>a"<esc>`<i"<esc>

" Map auto complete of (, ", ', [
inoremap $1 ()<esc>i
inoremap $2 []<esc>i
inoremap $3 {}<esc>i
inoremap $4 {<esc>o}<esc>O
inoremap $q ''<esc>i
inoremap $e ""<esc>i


" ---------------------------
"   S3f General abbreviations
" ---------------------------
iab xdate <c-r>=strftime("%d/%m/%y %H:%M:%S")<cr>

" ---------------------------
"   S3g Omni complete functions
" ---------------------------
autocmd FileType css set omnifunc=csscomplete#CompleteCSS

" ---------------------------
"   S3h Ack searching and cope displaying
"     requires ack.vim - it's much better than vimgrep/grep
" ---------------------------
" Use the the_silver_searcher if possible (much faster than Ack)
if executable('ag')
  let g:ackprg = 'ag --vimgrep --smart-case'
endif

" When you press gv you Ack after the selected text
vnoremap <silent> gv :call VisualSelection('gv', '')<CR>

" Open Ack and put the cursor in the right position
map <leader>g :Ack 

" When you press <leader>r you can search and replace the selected text
vnoremap <silent> <leader>r :call VisualSelection('replace', '')<CR>

" Do :help cope if you are unsure what cope is. It's super useful!
"
" When you search with Ack, display your results in cope by doing:
"   <leader>cc
"
" To go to the next search result do:
"   <leader>n
"
" To go to the previous search results do:
"   <leader>p
"
map <leader>cc :botright cope<cr>
map <leader>co ggVGy:tabnew<cr>:set syntax=qf<cr>pgg
map <leader>n :cn<cr>
map <leader>p :cp<cr>

" ---------------------------
"   S3i Helper functions
" ---------------------------
func! DeleteTillSlash()
    let g:cmd = getcmdline()

    if has("win16") || has("win32")
        let g:cmd_edited = substitute(g:cmd, "\\(.*\[\\\\]\\).*", "\\1", "")
    else
        let g:cmd_edited = substitute(g:cmd, "\\(.*\[/\]\\).*", "\\1", "")
    endif

    if g:cmd == g:cmd_edited
        if has("win16") || has("win32")
            let g:cmd_edited = substitute(g:cmd, "\\(.*\[\\\\\]\\).*\[\\\\\]", "\\1", "")
        else
            let g:cmd_edited = substitute(g:cmd, "\\(.*\[/\]\\).*/", "\\1", "")
        endif
    endif   

    return g:cmd_edited
endfunc

func! CurrentFileDir(cmd)
    return a:cmd . " " . expand("%:p:h") . "/"
endfunc




" ---------------------------
"   S5 Self Setting
" ---------------------------
"set isfname-=:
"set isfname-=:

" ---------------------------
"   S5a File I/O
" ---------------------------

"nnoremap gf :call GotoFile("new")<CR>
"nnoremap gb :call GotoFile("")<CR>

"open in a new tab
nnoremap gt <C-W>gf<CR>     
"open in a sp win
nnoremap gf <C-W>F<CR>
"nnoremap gg <C-W>F<CR>
nnoremap gd :vertical wincmd f<CR>
nnoremap ge :wincmd f<CR>
"for test ~/.vimrc
"for test $VIMRUNTIME/../../../Data/settings/_vimrc

" copy at windows
" nmap <C-V> "+gP
" imap <C-V> <ESC><C-V>a
vmap <C-C> "+y
nnoremap <C-a> :%y+ <CR>

" covert to html
" find a -exec vim {} -c "TOhtml" -c "w b/%:t" -c "wqa\!" \;

" Fast editing and reloading of vimrc configs
"

"if has("win16") || has("win32")
"    map <leader>e :e! $VIMRUNTIME/../../../Data/settings/vimfiles/my_vimrc/my_vimrc.vim<cr>
"    autocmd! bufwritepost vimrc source $VIMRUNTIME/../../../Data/settings/vimfiles/my_vimrc/my_vimrc.vim
"    map <leader>so :source $VIMRUNTIME/../../../Data/settings/vimfiles/my_vimrc/my_vimrc.vim<cr>
"else
    map <leader>e :e! $dotvim/my_vimrc.vim<cr>
    autocmd! bufwritepost vimrc source $dotvim/my_vimrc.vim
    map <leader>so :source $dotvim/my_vimrc.vim<cr>
"endif

" ---------------------------
"   S5b Search and replace
" ---------------------------
xnoremap / <ESC>/\%V
xnoremap ? <ESC>/\%V<C-R>/
" Visual Block replace
xnoremap s <ESC>:%s/\%V

" ---------------------------
"   S5c Display and GUI
" ---------------------------

set scrolloff=3      " 5 lines bevore and after the current line when scrolling
set nu               " 
set relativenumber   
set isfname-=,       " make , is a delimiter (for gf option)
set cursorline
"set cc=81
"let &colorcolumn="80,".join(range(120,999),",")
let &colorcolumn="80,"."160"

hi ColorColumn guibg=Black
hi clear CursorLine
hi CursorLine term=bold cterm=NONE ctermbg=darkblue guibg=Black
hi ColorColumn term=bold cterm=NONE ctermbg=darkblue guibg=Black
hi Search guibg=darkred
"hi Search guifg=blue guibg=yellow
"hi Search guibg=grey18

" Folding
set foldmethod=syntax
set foldcolumn=1
set foldlevelstart=20

"set foldclose
if has("gui_gtk2") && has("gui_running")
    set lines=50 columns=200
endif

let g:vim_markdown_folding_disabled=1 " Markdown
let javaScript_fold=1                 " JavaScript
let perl_fold=1                       " Perl
let php_folding=1                     " PHP
let r_syntax_folding=1                " R
let ruby_fold=1                       " Ruby
let sh_fold_enabled=1                 " sh
let vimsyn_folding='af'               " Vim script
let xml_syntax_folding=1              " XML

" display tab
set listchars=tab:»\ 
set list



" Change font size quickly
" http://vim.wikia.com/wiki/Change_font_size_quickly
" > Method 1
let s:pattern = '^\(.* \)\([1-9][0-9]*\)$'
let s:minfontsize = 6
let s:maxfontsize = 16
function! AdjustFontSize(amount)
  if has("gui_gtk2") && has("gui_running")
    let fontname = substitute(&guifont, s:pattern, '\1', '')
    let cursize = substitute(&guifont, s:pattern, '\2', '')
    let newsize = cursize + a:amount
    let percent = newsize/cursize
    let n_col   = &columns / percent
    let n_lines = &lines / percent
    if (newsize >= s:minfontsize) && (newsize <= s:maxfontsize)
      let newfont = fontname . newsize
      let &guifont = newfont
      let &columns = n_col
      let &lines   = n_lines
    endif
  else
    echoerr "You need to run the GTK2 version of Vim to use this function."
  endif
endfunction

function! LargerFont()
  call AdjustFontSize(1)
endfunction
command! LargerFont call LargerFont()

function! SmallerFont()
  call AdjustFontSize(-1)
endfunction
command! SmallerFont call SmallerFont()

nnoremap <C-Up>     :call AdjustFontSize(1)<CR>
nnoremap <C-Down>   :call AdjustFontSize(-1)<CR>

" > Method 2
"nnoremap <C-Up> :silent! let &guifont = substitute(
" \ &guifont,
" \ ':h\zs\d\+',
" \ '\=eval(submatch(0)+1)',
" \ '')<CR>
"nnoremap <C-Down> :silent! let &guifont = substitute(
" \ &guifont,
" \ ':h\zs\d\+',
" \ '\=eval(submatch(0)-1)',
" \ '')<CR>
"nnoremap <C-Up> :silent! let &guifont = substitute(
" \ &guifont,
" \ ' \zs\d\+',
" \ '\=eval(submatch(0)+2)',
" \ '')<CR>
"nnoremap <C-Down> :silent! let &guifont = substitute(
" \ &guifont,
" \ ' \zs\d\+',
" \ '\=eval(submatch(0)-2)',
" \ '')<CR>


" Restore screen size and position
" http://vim.wikia.com/wiki/Restore_screen_size_and_position
"
if has("gui_running")
  function! ScreenFilename()
    if has('amiga')
      return "s:.vimsize"
    elseif has('win32')
      return $HOME.'\_vimsize'
    else
      return $HOME.'/.vimsize'
    endif
  endfunction

  function! ScreenRestore()
    " Restore window size (columns and lines) and position
    " from values stored in vimsize file.
    " Must set font first so columns and lines are based on font size.
    let f = ScreenFilename()
    if has("gui_running") && g:screen_size_restore_pos && filereadable(f)
      let vim_instance = (g:screen_size_by_vim_instance==1?(v:servername):'GVIM')
      for line in readfile(f)
        let sizepos = split(line)
        if len(sizepos) == 5 && sizepos[0] == vim_instance
          silent! execute "set columns=".sizepos[1]." lines=".sizepos[2]
          silent! execute "winpos ".sizepos[3]." ".sizepos[4]
          return
        endif
      endfor
    endif
  endfunction

  function! ScreenSave()
    " Save window size and position.
    if has("gui_running") && g:screen_size_restore_pos
      let vim_instance = (g:screen_size_by_vim_instance==1?(v:servername):'GVIM')
      let data = vim_instance . ' ' . &columns . ' ' . &lines . ' ' .
            \ (getwinposx()<0?0:getwinposx()) . ' ' .
            \ (getwinposy()<0?0:getwinposy())
      let f = ScreenFilename()
      if filereadable(f)
        let lines = readfile(f)
        call filter(lines, "v:val !~ '^" . vim_instance . "\\>'")
        call add(lines, data)
      else
        let lines = [data]
      endif
      call writefile(lines, f)
    endif
  endfunction

  if !exists('g:screen_size_restore_pos')
    let g:screen_size_restore_pos = 1
  endif
  if !exists('g:screen_size_by_vim_instance')
    let g:screen_size_by_vim_instance = 1
  endif
  autocmd VimEnter * if g:screen_size_restore_pos == 1 | call ScreenRestore() | endif
  autocmd VimLeavePre * if g:screen_size_restore_pos == 1 | call ScreenSave() | endif
endif

" ---------------------------
"   S5d Other
" ---------------------------
function! HandleURL()
    let s:uri = matchstr(getline("."), '[a-z]*:\/\/[^ >,;]*')
    echo s:uri
    if s:uri != ""
        silent exec "!firefox '".s:uri."'"
    else
        echo "No URI found in line."
    endif
endfunction
map gx :call HandleURL()<cr><cr>




" ---------------------------
"   S8 Some Note
" ---------------------------

" Change Letter Case 
" ========================
" Using virtual block choose range  then   (e.g.  "HellO" )
"   g~  "hELLo" 
"   gU  "HELLO"   
"   gu  "hello"   


" Default Vim Useful Mapping
" ========================
" <C-F> | PageDown      | replace by CtrlP
" <C-B> | PageUp        | replace by CtrlP
" <C-D> | PageHalfDown
" <C-U> | PageHalfUp


" Highlight Given Column
" ========================
" set cc=32         " set colorcolumn=32
" set cc=0

" The Vim key notation for other special characters is listed below:
" ========================
" <BS>           Backspace
" <Tab>          Tab
" <CR>           Enter
" <Enter>        Enter
" <Return>       Enter
" <Esc>          Escape
" <Space>        Space
" <Up>           Up arrow
" <Down>         Down arrow
" <Left>         Left arrow
" <Right>        Right arrow
" <F1> - <F12>   Function keys 1 to 12
" #1, #2..#9,#0  Function keys F1 to F9, F10
" <Insert>       Insert
" <Del>          Delete
" <Home>         Home
" <End>          End
" <PageUp>       Page-Up
" <PageDown>     Page-Down
" <bar>          the '|' character, which otherwise needs to be escaped '\|'


" Mark
" ========================
" Command	Description
" ma	set mark a at current cursor location
" 'a	jump to line of mark a (first non-blank character in line)
" `a	jump to position (line and column) of mark a
" d'a	delete from current line to line of mark a
" d`a	delete from current cursor position to position of mark a
" c'a	change text from current line to line of mark a
" y`a	yank text to unnamed buffer from cursor to position of mark a
" :marks	list all the current marks
" :marks aB	list marks a, B
" ]'	jump to next line with a lowercase mark
" ['	jump to previous line with a lowercase mark
" ]`	jump to next lowercase mark
" [`	jump to previous lowercase mark
" `.	jump to position where last change occurred in current buffer
" `"	jump to position where last exited current buffer
" `0	jump to position in last file edited (when exited Vim)
" `1	like `0 but the previous file (also `2 etc)
" ''	jump back (to line in current buffer where jumped from)
" ``	jump back (to position in current buffer where jumped from)
" `[ or `]	jump to beginning/end of previously changed or yanked text
" `< or `>	jump to beginning/end of last visual selection


" Macros
" ========================
" qd	    start recording to register d
" q	        stop recording
" @d	    execute your macro
" @@	    execute your macro again
" :reg d    show the contents of registers d 
"
" =editing=
" Type :let @d=' (Note: Don't press <ENTER>)
" Press Ctrl-R Ctrl-R d to insert the current contents of register a .
" Edit the text as required.
" Append an apostrophe (') to finish the command, and press <Enter>.
" :reg d to view the new value in the register.
" Type @d to execute the contents of register d.




" ---------------------------
"   S9 SandBox
" ---------------------------

"let g:plantuml_executable_script='java -jar $VIMRUNTIME/../../../Data/settings/vimfiles/vimfiles/sources_self/vim-slumlord-master/plantuml.jar'
"nnoremap <F6> :w<CR> :silent make<CR>
"inoremap <F6> <Esc>:w<CR>:silent make<CR>
"vnoremap <F6> :<C-U>:w<CR>:silent make<CR
" =================================
" <C-a>
" 1
" 2
" =================================
" Virtual black
" prefix
" i_1
" i_12
" i_123
" surfix
" 1_$_a
" 12_$_a
" 123_$_a





