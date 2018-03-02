" ---------------------------------------------------------
"   my_vimrc.vim
"       https://github.com/pmewolf/my_vimrc

"   content
"       1.  Overwrite
"           1.1 Overwrite _vimrc
"           1.2 Overwrite basic.vim
"           1.3 Overwrite plugins_config
"           1.4 Overwrite extended.vim
"
"       2.  Self Setting
"           2.1 File I/O
"           2.2 Search and replace
"           2.3 Display and GUI
"           2.4 Other
"           2.5 For Programming
"
"       3.  Plugins Setting
"
"       4.  Plugins Usage
"           4.1 sources_forked
"           4.2 sources_non_forked
"           4.3 sources_self
"
"       8.  Some Note
"       
"       9.  SandBox
" ---------------------------------------------------------

"
if has("win16") || has("win32")
    behave mswin
    let $dotvim="$VIM/../../Data/settings/dotvim"
else
    let $dotvim="~/dotvim"
endif


" ---------------------------
" 1   Overwrite
" ---------------------------

" ---------------------------
" 1.1 Overwrite _vimrc
" ---------------------------
behave xterm
"behave mswin

" ---------------------------
" 1.2 Overwrite basic.vim
" ---------------------------
set statusline=\ %{HasPaste()}%F%m%r%h\ %w\ \ CWD:\ %r%{getcwd()}%h\ \ \ Line:\ %l,%v,%p%%
map <leader>tm :tabmove 
"map <C-i> :tabNext<cr>
"map <C-o> :tabnext<cr>
"map <C-o> :tabNext<cr>
map <C-p> :tabnext<cr>
set t_Co=256
"nmap <S-j> mz:m+<cr>`z
"nmap <S-k> mz:m-2<cr>`z
vmap <S-j> :m'>+<cr>`<my`>mzgv`yo`z
vmap <S-k> :m'<-2<cr>`>my`<mzgv`yo`z

set nowrap
"set wrap
" ----------------------------
" 1.3 Overwrite plugins_config
" ----------------------------

" " _ pathogen _
" 
" if has("win16") || has("win32")
" call pathogen#infect('sources_forked/{}')
" call pathogen#infect('sources_non_forked/{}')
" call pathogen#infect('sources_self/{}')
" call pathogen#infect('my_vimrc/{}')
" elseif
" call pathogen#infect('~/.vim/sources_forked/{}')
" call pathogen#infect('~/.vim/sources_non_forked/{}')
" call pathogen#infect('~/.vim/sources_self/{}')
" call pathogen#infect('~/.vim/my_vimrc/{}')
" endif
" call pathogen#helptags()


" _ yankring _
"
if has("win16") || has("win32")
    " Don't do anything
    let g:yankring_history_dir = '$VIMRUNTIME/../../../Data/settings/vimfiles/temp_dirs'
else
    let g:yankring_history_dir = '~/dotvim/temp_dirs'
endif




" ---------------------------
" 1.4 Overwrite extended.vim
" ---------------------------







" ---------------------------
" 2.  Self Setting
" ---------------------------
"set isfname-=:
"set isfname-=:

" ---------------------------
" 2.1 File I/O
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


set backup
" Turn persistent undo on means that you can undo even when you close a buffer/VIM
set undofile
if has("win16") || has("win32")
    set backupdir=$VIM/../../Data/settings/dotvim/temp_dirs/back,.
    set directory=$VIM/../../Data/settings/dotvim/temp_dirs/swp,.
    set undodir=$VIM/../../Data/settings/dotvim/temp_dirs/undodir
else
    set backupdir=~/dotvim/temp_dirs/back,.
    set directory=~/dotvim/temp_dirs/swp,.
    set undodir=~/dotvim/temp_dirs/undodir
endif

" ---------------------------
" 2.2 Search and replace
" ---------------------------
xnoremap / <ESC>/\%V
xnoremap ? <ESC>/\%V<C-R>/
" Visual Block replace
xnoremap s <ESC>:%s/\%V

" ---------------------------
" 2.3 Display and GUI
" ---------------------------
colorscheme peaksea
"colorscheme ir_black
"colorscheme desert

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


" Set font according to system
if has("mac") || has("macunix")
    set gfn=Menlo:h15
elseif has("win16") || has("win32")
    set gfn=Consolas:h12:cANSI
    "set gfn=Courier:h14:cANSI
elseif has("linux") || has("unix")
    set gfn=Monospace\ 12
    "set gfn=inconsolata\ 12
    "set gfn=DejaVu\ Sans\ Mono\ 12
endif

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
" 2.4 Other
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
" 2.5 For Programming
" ---------------------------


" _ Verilog/SystemVerilog _ 

" Parenthesis/bracket
inoremap $B begin<esc>oend<esc>O

" Syntax
"if has("win16") || has("win32")
"    augroup syntax
"    au BufNewFile,BufReadPost *.v*      so $VIMRUNTIME\..\..\..\data\settings\vimfiles\sources_self\verilog_systemverilog\syntax\verilog_systemverilog.vim 
"    au BufNewFile,BufReadPost *.sv*     so $VIMRUNTIME\..\..\..\data\settings\vimfiles\sources_self\verilog_systemverilog\syntax\verilog_systemverilog.vim
"    au BufNewFile,BufReadPost *.h*      so $VIMRUNTIME\..\..\..\data\settings\vimfiles\sources_self\verilog_systemverilog\syntax\verilog_systemverilog.vim
"    au BufNewFile,BufReadPost *.log     so $VIMRUNTIME\..\..\..\data\settings\vimfiles\sources_self\verilog_systemverilog\syntax\verilog_systemverilog.vim
"    augroup END
"    nmap sv :so $VIMRUNTIME\..\..\..\data\settings\vimfiles\sources_self\verilog_systemverilog\syntax\verilog_systemverilog.vim<CR>
"else
    augroup syntax
    au BufNewFile,BufReadPost *.v*      so $dotvim/bundle/verilog_systemverilog.vim/syntax/verilog_systemverilog.vim 
    au BufNewFile,BufReadPost *.sv*     so $dotvim/bundle/verilog_systemverilog.vim/syntax/verilog_systemverilog.vim
    au BufNewFile,BufReadPost *.h*      so $dotvim/bundle/verilog_systemverilog.vim/syntax/verilog_systemverilog.vim
    au BufNewFile,BufReadPost *.log     so $dotvim/bundle/verilog_systemverilog.vim/syntax/verilog_systemverilog.vim
    augroup END
    nmap sv :so $dotvim/bundle/verilog_systemverilog.vim/syntax/verilog_systemverilog.vim<CR>
"endif

augroup syntax
"au BufNewFile,BufReadPost *.sv* so $VIMRUNTIME/../../../Data/settings/vimfiles/syntax/systemverilog.vim
au BufNewFile,BufReadPost *.sv* so $dotvim/bundle/verilog_systemverilog.vim/syntax/systemverilog.vim
augroup END


" _ Python _ 
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


" _ cscope _
set cscopetag
set csto=0

"if filereadable("cscope.out")
"   cs add cscope.out   
"elseif $CSCOPE_DB != ""
"    cs add $CSCOPE_DB
"endif
"set cscopeverbose
"
"nmap zs :cs find s <C-R>=expand("<cword>")<CR><CR>
"nmap zg :cs find g <C-R>=expand("<cword>")<CR><CR>
"nmap zc :cs find c <C-R>=expand("<cword>")<CR><CR>
"nmap zt :cs find t <C-R>=expand("<cword>")<CR><CR>
"nmap ze :cs find e <C-R>=expand("<cword>")<CR><CR>
"nmap zf :cs find f <C-R>=expand("<cfile>")<CR><CR>
"nmap zi :cs find i ^<C-R>=expand("<cfile>")<CR>$<CR>
"nmap zd :cs find d <C-R>=expand("<cword>")<CR><CR>


" ---------------------------
" 3.  Plugins Setting 
" ---------------------------

" _ Calendar _
"
" let g:calendar_frame = 'default'
" let g:calendar_google_calendar = 1
" let g:calendar_google_task = 1



" _ ConqueTerm _
"
let g:ConqueTerm_PyExe = '..\Python3251\App\python.exe'

" _ indentLine _
" Vim
let g:indentLine_color_term = 239

" GVim
"let g:indentLine_color_gui = '#A4E57E'

" none X terminal
let g:indentLine_color_tty_light = 7 " (default: 4)
let g:indentLine_color_dark = 1 " (default: 2)

" Background (Vim, GVim)
let g:indentLine_bgcolor_term = 202
let g:indentLine_bgcolor_gui = '#FF5F00'
if has("gui_running") 
else
    let g:indentLine_char = '|'
endif


" _ Match_it _
"
if exists('loaded_matchit')
let b:match_ignorecase=0
let b:match_words=
  \ '\<begin\>:\<end\>,' .
  \ '\<if\>:\<else\>,' .
  \ '\<module\>:\<endmodule\>,' .
  \ '\<class\>:\<endclass\>,' .
  \ '\<program\>:\<endprogram\>,' .
  \ '\<clocking\>:\<endclocking\>,' .
  \ '\<property\>:\<endproperty\>,' .
  \ '\<sequence\>:\<endsequence\>,' .
  \ '\<package\>:\<endpackage\>,' .
  \ '\<covergroup\>:\<endgroup\>,' .
  \ '\<primitive\>:\<endprimitive\>,' .
  \ '\<specify\>:\<endspecify\>,' .
  \ '\<generate\>:\<endgenerate\>,' .
  \ '\<interface\>:\<endinterface\>,' .
  \ '\<function\>:\<endfunction\>,' .
  \ '\<task\>:\<endtask\>,' .
  \ '\<case\>\|\<casex\>\|\<casez\>:\<endcase\>,' .
  \ '\<fork\>:\<join\>\|\<join_any\>\|\<join_none\>,' .
  \ '`ifdef\>:`else\>:`endif\>,'
endif

" _ Pydiction _
let g:pydiction_location = '$VIMRUNTIME/../../../Data/settings/vimfiles/sources_self/Pydiction/complete-dict' 
"let g:pydiction_menu_height = 8



" _ Syntastic _
let g:syntasic_check_on_open = 1

" _ Tagbar _
" Open and close the tagbar separately
nmap <F5> :TagbarToggle<CR>
"nmap <F4> :SrcExplToggle<CR>


" _ Trinity _
" Open and close all the three plugins on the same time
nmap <F8>  :TrinityToggleAll<CR>
" Open and close the Taglist separately
nmap <F9> :TrinityToggleTagList<CR>
" Open and close the NERD Tree separately
nmap <F10> :TrinityToggleNERDTree<CR>
" Open and close the Source Explorer separately
"nmap <F11>  :TrinityToggleSourceExplorer<CR>


" _ VimWiki _
"
" let g:vimwiki_folding = 1
" let g:vimwiki_fold_lists = 'expr'
let g:vimwiki_folding = 'expr' 
" template from https://github.com/xiongjia/recycle.bin
"
let g:vimwiki_list = [
                    \ {'path':'~/vimwiki/_content/',
                    \  'path_html':'~/vimwiki/output', 
                    \  'template_path': '~/vimwiki/_config/', 
                    \  'template_default': 'vimwiki', 
                    \  'template_ext': '.tpl', 
                    \  'nested_syntaxes':{
                    \       'c': 'c',
                    \       'cpp': 'cpp',
                    \       'java': 'java',
                    \       'python': 'python',
                    \       'systemverilog': 'systemverilog',
                    \  },
                    \  'auto_export':0
                    \},
                    \{ 'path':'~/vimwiki/_content_ex/',
                    \  'path_html':'~/vimwiki/output_ex', 
                    \  'template_path': '~/vimwiki/_config/', 
                    \  'template_default': 'vimwiki', 
                    \  'template_ext': '.tpl', 
                    \  'auto_export':0
                    \}] 
inoremap $T %title   <esc>mAi<cr>%toc<esc>`A


" _ WinManager _
"
let g:NERDTree_title="[NERDTree]"
"let g:winManagerWindowLayout = "BufExplorer,FileExplorer|TagList"
"let g:winManagerWindowLayout = "TagList|FileExplorer,BufExplorer"
"let g:winManagerWindowLayout = "NERDTree|TagList"
"let g:winManagerWindowLayout = "NERDTree|BufExplorer"
let g:winManagerWindowLayout='NERDTree|TagList,BufExplorer' " ctrl+n to switch from taglist to bufexplorer

let g:winManagerWidth = 30
"let g:winManagerAutoOpen = 1

function! NERDTree_Start()  
    exec 'NERDTree'  
endfunction  
function! NERDTree_IsValid()  
    return 1  
endfunction  
"nmap <silent> <F8> :WMToggle<cr>
nmap wm :WMToggle<CR>  


" ---------------------------
" 4.  Plugins Usage
" ---------------------------

" ---------------------------
" 4.1 sources_forked
" ---------------------------

" _ MRU(Most Recent Used) _
" ========================
" <leader>f 


" ---------------------------
" 4.2 sources_non_forked
" ---------------------------



" ---------------------------
" 4.3 sources_self
" ---------------------------


" _ Ctags and taglist _
" ========================
" Ctrl + ]      : enter funcition body
" Ctrl + t      : go back to where u leave

" _ Calendar _
" ========================
" :Calendar 
" :Calendar 2015 1 8
" :Calendar -view=year
" :Calendar -view=year -split=vertical -width=27
" :Calendar -view=year -split=horizontal -position=below -height=12
" :Calendar -first_day=monday
" :Calendar -view=clock



" _ Pydiction _
" ========================
" <Space>       : Accept current match and insert a space.
" <C-Y>         : Accept current match and and don't insert a space.
" <Enter>       : Accept current match and insert a newline.
" <ESC>or<C-E>  : Close the menu and do not accept any match.
" :help popupmenu-keys

" _ Shell _
" ========================
" <F11>         : to Fullscreen


" _ VimWiki _
" ========================
" <leader>wt    : to open wiki

" _ WinManager _
" ========================
" wm            : to use it


" ---------------------------
" 8.  Some Note
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
" 9.  SandBox
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





