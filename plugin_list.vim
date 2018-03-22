"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" plugin on GitHub repo
Plugin 'tpope/vim-fugitive'

Plugin 'maxbrunsfeld/vim-yankstack'
    " Purpose:
    " Usage: 
    " Config:
    let g:yankstack_yank_keys = ['y', 'd']
    
    nmap <c-p> <Plug>yankstack_substitute_older_paste
    nmap <c-n> <Plug>yankstack_substitute_newer_paste

Plugin 'vim-scripts/YankRing.vim'
    " Purpose:
    " Usage: 
    " Config:
    if has("win16") || has("win32")
        " Don't do anything
        let g:yankring_history_dir = '$VIMRUNTIME/../../../Data/settings/vimfiles/temp_dirs'
    else
        let g:yankring_history_dir = '~/dotvim/temp_dirs'
    endif


"Plugin 'tpope/vim-pathogen'
"    " Purpose:
"    " Usage: 
"    " Config:
"    let s:vim_runtime = expand('<sfile>:p:h')."/.."
"    call pathogen#infect(s:vim_runtime.'/sources_forked/{}')
"    call pathogen#infect(s:vim_runtime.'/sources_non_forked/{}')
"    call pathogen#infect(s:vim_runtime.'/my_plugins/{}')
"    call pathogen#helptags()


Plugin 'mileszs/ack.vim'

Plugin 'ctrlpvim/ctrlp.vim'
    " Purpose:
    " Usage: 
    " Config:
    let g:ctrlp_working_path_mode = 0
    
    let g:ctrlp_map = '<c-f>'
    map <leader>j :CtrlP<cr>
    map <c-b> :CtrlPBuffer<cr>
    
    let g:ctrlp_max_height = 20
    let g:ctrlp_custom_ignore = 'node_modules\|^\.DS_Store\|^\.git\|^\.coffee'

Plugin 'vim-scripts/mayansmoke'
    
Plugin 'chr4/nginx.vim'

Plugin 'scrooloose/snipmate-snippets'
    " Purpose:
    " Usage: 
    " Config:
    ino <c-j> <c-r>=snipMate#TriggerSnippet()<cr>
    snor <c-j> <esc>i<right><c-r>=snipMate#TriggerSnippet()<cr>

Plugin 'vim-scripts/tlib'
Plugin 'MarcWeber/vim-addon-mw-utils'
Plugin 'sophacles/vim-bundle-mako'
Plugin 'altercation/vim-colors-solarized'
Plugin 'michaeljsmith/vim-indent-object'
Plugin 'groenewege/vim-less'
Plugin 'therubymug/vim-pyte'
Plugin 'garbas/vim-snipmate'
Plugin 'honza/vim-snippets'
Plugin 'tpope/vim-surround'
    " Purpose:
    " Usage: 
    " Config:
    vmap Si S(i_<esc>f)
    au FileType mako vmap Si S"i${ _(<esc>2f"a) }<esc>

Plugin 'terryma/vim-expand-region'

Plugin 'terryma/vim-multiple-cursors'
    " Purpose:
    " Usage: 
    " Config:
    let g:multi_cursor_next_key="\<C-s>"

Plugin 'junegunn/goyo.vim'
    " Purpose:
    " Usage: 
    " Config:
    let g:goyo_width=100
    let g:goyo_margin_top = 2
    let g:goyo_margin_bottom = 2
    nnoremap <silent> <leader>z :Goyo<cr>

Plugin 'amix/vim-zenroom2'

Plugin 'dpino/zencoding-vim'
    " Purpose:
    "   zencoding-vim is vim script support for expanding abbreviation like zen-coding(emmet).
    " Usage: 
    " Config:
    " Enable all functions in all modes
    let g:user_zen_mode='a'

Plugin 'tpope/vim-repeat'
Plugin 'tpope/vim-commentary'
Plugin 'fatih/vim-go'
    " Purpose:
    " Usage: 
    " Config:
    let g:go_fmt_command = "goimports"
    
Plugin 'airblade/vim-gitgutter'
    " Purpose:
    " Usage: 
    " Config:
    let g:gitgutter_enabled=0
    nnoremap <silent> <leader>d :GitGutterToggle<cr>
    
Plugin 'morhetz/gruvbox'
Plugin 'digitaltoad/vim-pug'
Plugin 'itchyny/lightline.vim'
    " Purpose:
    " Usage: 
    " Config:
    let g:lightline = {
          \ 'colorscheme': 'wombat',
          \ }
    
    let g:lightline = {
          \ 'colorscheme': 'wombat',
          \ 'active': {
          \   'left': [ ['mode', 'paste'],
          \             ['fugitive', 'readonly', 'filename', 'modified'] ],
          \   'right': [ [ 'lineinfo' ], ['percent'] ]
          \ },
          \ 'component': {
          \   'readonly': '%{&filetype=="help"?"":&readonly?"🔒":""}',
          \   'modified': '%{&filetype=="help"?"":&modified?"+":&modifiable?"":"-"}',
          \   'fugitive': '%{exists("*fugitive#head")?fugitive#head():""}'
          \ },
          \ 'component_visible_condition': {
          \   'readonly': '(&filetype!="help"&& &readonly)',
          \   'modified': '(&filetype!="help"&&(&modified||!&modifiable))',
          \   'fugitive': '(exists("*fugitive#head") && ""!=fugitive#head())'
          \ },
          \ 'separator': { 'left': ' ', 'right': ' ' },
          \ 'subseparator': { 'left': ' ', 'right': ' ' }
          \ }

"Plugin 'tpope/tpope-vim-abolish'

Plugin 'vim-scripts/mru.vim'
    " Purpose:
    "   Most Recent Used
    " Usage: 
    "   <leader> f
    " Config:
    let MRU_Max_Entries = 400
    map <leader>f :MRU<CR>

"""
"Plugin 'shemerey/vim-peepopen'
Plugin 'pmewolf/PeepOpen-EditorSupport', {'rtp': 'vim-peepopen/'}

" My plugin
Plugin 'tpope/vim-abolish'


Plugin 'vim-scripts/Conque-Shell'
    " Config:
    let g:ConqueTerm_PyExe = '..\Python3251\App\python.exe'

Plugin 'Yggdroot/indentLine'
    " Config:
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

Plugin 'tmhedberg/matchit'
    " Config:
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

Plugin 'xolox/vim-misc'


Plugin 'tpope/vim-dispatch'
Plugin 'powerline/powerline'

Plugin 'othree/xml.vim'
Plugin 'othree/vim-slumlord'

" -------------------------------------
" VIM Scheme
" -------------------------------------
Plugin 'twerth/ir_black'
Plugin 'vim-scripts/peaksea'

" -------------------------------------
" IDE related
" -------------------------------------
Plugin 'xolox/vim-shell'
    " Purpose:
    " Usage: 
    "   <F11>           : to Fullscreen

Plugin 'amix/open_file_under_cursor.vim'

Plugin 'scrooloose/nerdtree'
    " Purpose:
    " Usage: 
    " Config:
    let g:NERDTreeWinPos = "right"
    let NERDTreeShowHidden=0
    let NERDTreeIgnore = ['\.pyc$', '__pycache__']
    let g:NERDTreeWinSize=35
    map <leader>nn :NERDTreeToggle<cr>
    map <leader>nb :NERDTreeFromBookmark<Space>
    map <leader>nf :NERDTreeFind<cr>

Plugin 'majutsushi/tagbar'
    " Purpose:
    " Usage: 
    " Config:
    " Open and close the tagbar separately
    nmap <F5> :TagbarToggle<CR>
    "nmap <F4> :SrcExplToggle<CR>

Plugin 'vim-scripts/taglist.vim'
    " Purpose:
    "   ctags with taglist
    " Usage: 
    "   ${trace_files_dir}> ctags -R
    "   -------------------------------
    "   Ctrl + ]      : enter funcition body
    "   Ctrl + t      : go back to where u leave
    set tags=./tags,./TAGS,tags;~,TAGS;~
    "nmap <F8> :TlistToggle<CR><CR>     "將F8設為開啟taglist的快捷鍵
    let Tlist_Show_One_File=1           "只顯示當下瀏覽檔案的func，不顯示之前瀏覽的檔案
    let Tlist_Exit_OnlyWindow=1         "如果taglist區塊是最後一個，則退出vim
    set ut=100                          "更新速度設成100ms

Plugin 'wesleyche/SrcExpl'
    " Purpose:
    " Usage: 
    " Config:
    "nmap <F10> :SrcExplToggle<CR>
    let g:SrcExpl_pluginList = [ 
        \ "__Tag_List__", 
        \ "_NERD_tree_", 
        \ "Source_Explorer" 
    \ ] 

Plugin 'vim-scripts/Trinity'
    " Purpose:
    " Usage: 
    " Config:
    " Open and close all the three plugins on the same time
    nmap <F8>  :TrinityToggleAll<CR>
    " Open and close the Taglist separately
    nmap <F9> :TrinityToggleTagList<CR>
    " Open and close the NERD Tree separately
    nmap <F10> :TrinityToggleNERDTree<CR>
    " Open and close the Source Explorer separately
    "nmap <F11>  :TrinityToggleSourceExplorer<CR>

Plugin 'wolfpython/cscope_map.vim'
    " Purpose:
    "   ~/dotvim/bundle/cscope_map.vim/plugin/cscope_maps.vim
    " Usage: 
    "   ${trace_files_dir}> cscope -Rbqk
    "
    "   :cs find s {name} : 找出C語言name的符號
    "   :cs find g {name} : 找出name定義的地方
    "   :cs find c {name} : 找出使用name的地方
    "   :cs find t {name} : 找出name的字串
    "   :cs find e {name} : 相當於egrep功能，但速度更佳
    "   :cs find f {name} : 尋找檔案
    "   :cs find i {name} : 尋找include此檔案的檔案
    "   :cs find d {name} : 尋找name裡面使用到的函式
    "   <CTRL-\>s  # symbol:    find all references to the token under cursor
    "   <CTRL-\>g  # global:    find global definition(s) of the token under cursor
    "   <CTRL-\>c  # calls:     find all calls to the function name under cursor
    "   <CTRL-\>t  # text:      find all instances of the text under cursor
    "   <CTRL-\>e  # egrep:     egrep search for the word under cursor
    "   <CTRL-\>f  # file:      open the filename under cursor
    "   <CTRL-\>i  # includes:  find files that include the filename under cursor
    "   <CRTL-\>d  # called:    find functions that function under cursor calls    
    " Config:
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
    nmap zs :cs find s 
    nmap zg :cs find g 
    nmap zc :cs find c 
    nmap zt :cs find t 
    nmap ze :cs find e 
    nmap zf :cs find f 
    nmap zi :cs find i 
    nmap zd :cs find d 


Plugin 'corntrace/bufexplorer'
    " Purpose:
    " Usage: 
    " Config:
    let g:bufExplorerDefaultHelp=0
    let g:bufExplorerShowRelativePath=1
    let g:bufExplorerFindActive=1
    let g:bufExplorerSortBy='name'
    map <leader>o :BufExplorer<cr>

Plugin 'vim-scripts/winmanager'
    " Purpose:
    " Usage:
    "   wm  : open winmanager
    " Config:
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


" -------------------------------------
" Programming Assist
" -------------------------------------

Plugin 'vim-scripts/AutoComplPop'
Plugin 'jiangmiao/auto-pairs'
Plugin 'scrooloose/syntastic'
    " Purpose:
    "   Syntax Checker
    " Usage: 
    " Config:
    " Python
    let g:syntastic_python_checkers=['pyflakes']
    
    " Javascript
    let g:syntastic_javascript_checkers = ['jshint']
    
    " Go
    let g:syntastic_auto_loc_list = 1
    let g:syntastic_go_checkers = ['go', 'golint', 'errcheck']
    
    " Custom CoffeeScript SyntasticCheck
    func! SyntasticCheckCoffeescript()
        let l:filename = substitute(expand("%:p"), '\(\w\+\)\.coffee', '.coffee.\1.js', '')
        execute "tabedit " . l:filename
        execute "SyntasticCheck"
        execute "Errors"
    endfunc
    nnoremap <silent> <leader>c :call SyntasticCheckCoffeescript()<cr>
    let g:syntasic_check_on_open = 1

Plugin 'vhda/verilog_systemverilog.vim'
    " Purpose:
    " Usage: 
    " Config:
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
au BufNewFile,BufReadPost *.sv* so $dotvim/bundle/verilog_systemverilog.vim/syntax/verilog_systemverilog.vim
augroup END

    
Plugin 'plasticboy/vim-markdown'
"Plugin 'tpope/vim-markdown'
Plugin 'hdima/python-syntax'
Plugin 'nvie/vim-flake8'
Plugin 'vim-scripts/Pydiction'
    " Purpose:
    " Usage: 
    "   <Space>         : Accept current match and insert a space.
    "   <C-Y>           : Accept current match and and don't insert a space.
    "   <Enter>         : Accept current match and insert a newline.
    "   <ESC>or<C-E>    : Close the menu and do not accept any match.
    "   :help popupmenu-keys
    " Config:
    let g:pydiction_location = '$VIMRUNTIME/../../../Data/settings/vimfiles/sources_self/Pydiction/complete-dict' 
    "let g:pydiction_menu_height = 8
Plugin 'artur-shaik/vim-javacomplete2'
"Plugin 'kchmck/vim-coffee-script'

"Plugin 'aklt/plantuml-syntax'


" -------------------------------------
" Utility
" -------------------------------------
Plugin 'itchyny/calendar.vim'
    " Purpose:
    " Usage: 
    "   :Calendar 
    "   :Calendar 2015 1 8
    "   :Calendar -view=year
    "   :Calendar -view=year -split=vertical -width=27
    "   :Calendar -view=year -split=horizontal -position=below -height=12
    "   :Calendar -first_day=monday
    "   :Calendar -view=clock
    " Config:
    "let g:calendar_frame = 'default'
    "let g:calendar_google_calendar = 1
    "let g:calendar_google_task = 1

Plugin 'vimwiki/vimwiki'
    " Purpose:
    " Usage: 
    "   <leader>wt  : to open wiki
    " Config:
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

"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" plugin from http://vim-scripts.org/vim/scripts.html
Plugin 'L9'

" Git plugin not hosted on GitHub
Plugin 'git://git.wincent.com/command-t.git'

" git repos on your local machine (i.e. when working on your own plugin)
"Plugin 'file:///home/gmarik/path/to/plugin'

" The sparkup vim script is in a subdirectory of this repo called vim.
" Pass the path to set the runtimepath properly.
Plugin 'rstacruz/sparkup', {'rtp': 'vim/'}

" Install L9 and avoid a Naming conflict if you've already installed a
" different version somewhere else.
" Plugin 'ascenator/L9', {'name': 'newL9'}
