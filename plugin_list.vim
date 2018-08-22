" -----------------------------------------------------------------------------
"   plugin_list.vim
"       https://github.com/pmewolf/dotvim
"
"   Contents
"       VIM_Enhancement
"       ColorScheme
"       Search
"       IDE_Related
"       SyntaxRelated
"       Programming_Assist
"       Utility
" -----------------------------------------------------------------------------
"
"Plugin 'VundleVim/Vundle.vim'
    " Purpose:
    "   Vundle, the plug-in manager for Vim
    "   http://github.com/VundleVim/Vundle.Vim
    " Usage:
    "   :PluginInstall
    "   :PluginUpate
    "   :PluginClean
    "   :PluginList
    " Config:
" -----------------------------------------------------------------------------
" Vundle Example
"   https://github.com/VundleVim/Vundle.vim/wiki/Examples
" -----------------------------------------------------------------------------
"" plugin on GitHub repo
"Plugin 'tpope/vim-fugitive'
"
"" plugin from http://vim-scripts.org/vim/scripts.html
"Plugin 'L9'
"
"" Git plugin not hosted on GitHub
"Plugin 'git://git.wincent.com/command-t.git'
"
"" git repos on your local machine (i.e. when working on your own plugin)
"Plugin 'file:///home/gmarik/path/to/plugin'
"
"" The sparkup vim script is in a subdirectory of this repo called vim.
"" Pass the path to set the runtimepath properly.
"Plugin 'rstacruz/sparkup', {'rtp': 'vim/'}
"
"" Install L9 and avoid a Naming conflict if you've already installed a
"" different version somewhere else.
"Plugin 'ascenator/L9', {'name': 'newL9'}
" -----------------------------------------------------------------------------

Plugin 'tpope/vim-fugitive'
    " Purpose:
    "   fugitive.vim: a Git wrapper so awesome, it should be illegal
    "   https://www.vim.org/scripts/script.php?script_id=2975
    "   #utility #git
    " Usage:
    "   :Gdiff
    "       to bring up the staged version of the file side by side with the
    "       working tree version and use Vim's diff handling capabilities to
    "       stage a subset of the file's changes.
    "   :Gstatus
    "       Press `-` to add/reset a file's changes, or `p` to add/reset
    "       --patch
    "   :Gblame
    "       brings up an interactive vertical split with git-blame output.
    "       Press enter on a line to reblame the file as it stood in that
    "       commit, or`o` to open that commit in a split.
    "   :Gmove
    "       does a git-mv on a file and simultaneously renames the buffer.
    "   :Gremove
    "       does a git-rm on a file and simultaneously deletes the buffer.
    "   :Ggrep
    "       to search the work tree (or any arbitrary commit) with git-grep,
    "       skipping over that which is not tracked in the repository.
    "   :Glog
    "       loads all previous revisions of a file into the quickfix list so
    "       you can iterate over them and watch the file evolve!
    "   :Gread
    "       is a variant of `git checkout -- filename` that operates on the
    "       buffer rather than the filename.
    "       This means you can use `u` to undo it and you never get any
    "       warnings about the file changing outside Vim.
    "   :Gwrite
    "       writes to both the work tree and index versions of a file, making
    "       it like git-add when called from a work tree file and like
    "       git-checkout when called from the index or a blob in history.
    "   :Git
    "       for running any arbitrary command.
    "
    " Config:
    "   Add %{fugitive#statusline()} to 'statusline' to get an indicator with
    "   the current branch in (surprise!) your statusline.



Plugin 'michaeljsmith/vim-indent-object'
    " Purpose:
    "   Vim plugin that defines a new text object representing lines of code at
    "   the same indent level. Useful for python/vim scripts, etc.
    "   https://www.vim.org/scripts/script.php?script_id=3037
    "   #utility #python
    " Usage:
    " Config:

Plugin 'tpope/vim-surround'
    " Purpose:
    "   surround.vim: quoting/parenthesizing made simple
    "   https://www.vim.org/scripts/script.php?script_id=1697
    "   #utility
    " Usage:
    " Config:
    vmap Si S(i_<esc>f)
    au FileType mako vmap Si S"i${ _(<esc>2f"a) }<esc>

Plugin 'terryma/vim-expand-region'
    " Purpose:
    "   Vim plugin that allows you to visually select increasingly larger
    "   regions of text using the same key combination
    " Usage:
    "   Press + to expand the visual selection and _ to shrink it.
    " Config:
    "map K <Plug>(expand_region_expand)
    "map J <Plug>(expand_region_shrink)

Plugin 'terryma/vim-multiple-cursors'
    " Purpose:
    "   True Sublime Text style multiple selections for Vim
    "   https://github.com/terryma/vim-multiple-cursors
    " Usage:
    " Config:
    let g:multi_cursor_next_key="\<C-s>"

Plugin 'junegunn/goyo.vim'
    " Purpose:
    "   Distraction-free writing in Vim
    " Usage:
    " Config:
    let g:goyo_width=100
    let g:goyo_margin_top = 2
    let g:goyo_margin_bottom = 2
    nnoremap <silent> <leader>z :Goyo<cr>

Plugin 'amix/vim-zenroom2'
    " Purpose:
    "   A Vim extension that emulates iA Writer environment when editing
    "   Markdown, reStructuredText or text files
    "   It requires goyo.vim and it works by setting global Goyo callbacks that
    "   triggers special setup for Markdown, reStructuredText and text files.
    " Usage:
    " Config:

Plugin 'tpope/vim-repeat'
    " Purpose:
    "   repeat.vim: enable repeating supported plugin maps with "."
    "   https://www.vim.org/scripts/script.php?script_id=2136
    "   #utility
    " Usage:
    " Config:

Plugin 'tpope/vim-commentary'
    " Purpose:
    "   commentary.vim: comment stuff out
    "   https://www.vim.org/scripts/script.php?script_id=3695
    "   #utility
    " Usage:
    " Config:
    
Plugin 'airblade/vim-gitgutter'
    " Purpose:
    "   A Vim plugin which shows a git diff in the gutter (sign column) and
    "   stages/undoes hunks.
    "   https://github.com/airblade/vim-gitgutter
    " Usage:
    " Config:
    let g:gitgutter_enabled=0
    nnoremap <silent> <leader>d :GitGutterToggle<cr>
 

Plugin 'vim-scripts/mru.vim'
    " Purpose:
    "   Plugin to manage Most Recently Used (MRU) files
    " Usage:
    "   <leader> f
    " Config:
    let MRU_Max_Entries = 400
    map <leader>f :MRU<CR>


"Plugin 'shemerey/vim-peepopen'
"    " Purpose:
"    "   A plugin for the Vim text editor. PeepOpen provides fuzzy search of
"    "   filenames and paths in a programming project.
"    " Usage:
"    " Config:
Plugin 'pmewolf/PeepOpen-EditorSupport', {'rtp': 'vim-peepopen/'}
    " Purpose:
    " Usage:
    " Config:


Plugin 'vim-scripts/Conque-Shell'
    " Purpose:
    "   Run interactive commands inside a Vim buffer
    "   https://www.vim.org/scripts/script.php?script_id=2771
    " Usage:
    " Config:
    let g:ConqueTerm_PyExe = '..\Python3251\App\python.exe'

Plugin 'Yggdroot/indentLine'
    " Purpose:
    "   A vim plugin to display the indention levels with thin vertical lines
    "   https://github.com/Yggdroot/indentLine
    " Usage:
    " Config:
    "" highlight conceal color
    "let g:indentLine_setColors = 0

    "" customize conceal color
    "    " Vim
    "    let g:indentLine_color_term = 239
    "    " GVim let g:indentLine_color_gui = '#A4E57E'
    "    " none X terminal
    "    let g:indentLine_color_tty_light = 7 " (default: 4)
    "    let g:indentLine_color_dark = 1 " (default: 2)
    "
    "    " Background (Vim, GVim)
    "    let g:indentLine_bgcolor_term = 202
    "    let g:indentLine_bgcolor_gui = '#FF5F00'
    
    if !has("gui_running")
        let g:indentLine_char = '|'
    endif

Plugin 'tmhedberg/matchit'
    " Purpose:
    "   extended % matching for HTML, LaTeX, and many other languages
    "   https://www.vim.org/scripts/script.php?script_id=39
    "   #utility
    " Usage:
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
    " Purpose:
    "   Miscellaneous auto-load Vim scripts
    "   http://peterodding.com/code/vim/misc/
    "   https://github.com/xolox/vim-misc
    "   #utility
    " Usage:
    " Config:

Plugin 'tpope/vim-dispatch'
    " Purpose:
    "   dispatch.vim: asynchronous build and test dispatcher
    "   https://www.vim.org/scripts/script.php?script_id=4504
    "   https://vimeo.com/63116209
    "   https://github.com/tpope/vim-dispatch
    "   #utility
    " Usage:
    " Config:

Plugin 'powerline/powerline'
    " Purpose:
    "   Powerline is a statusline plugin for vim, and provides statuslines and
    "   prompts for several other applications, including zsh, bash, tmux,
    "   IPython, Awesome and Qtile.
    "   https://powerline.readthedocs.io/en/latest/
    " Usage:
    " Config:

Plugin 'vim-airline/vim-airline'
    " Purpose:
    "   lean & mean status/tabline for vim that's light as air
    " Usage:
    " Config:
    " set status line
    set laststatus=2
    " enable powerline-fonts
    if has("mac") || has("macunix")
        let g:airline_powerline_fonts = 1
    endif
    " enable tabline
    let g:airline#extensions#tabline#enabled = 1
    " set left separator
    let g:airline#extensions#tabline#left_sep = ' '
    " set left separator which are not editting
    let g:airline#extensions#tabline#left_alt_sep = '|'
    " show buffer number
    let g:airline#extensions#tabline#buffer_nr_show = 1
    "
    let g:airline#extensions#tabline#formatter = 'unique_tail'
Plugin 'vim-airline/vim-airline-themes'
    " Purpose:
    "   A collection of themes for vim-airline
    " Usage:
    " Config:
    " set theme ref https://github.com/vim-airline/vim-airline/wiki/Screenshots
    "let g:airline_theme='badwolf'
    let g:airline_theme='powerlineish'
    "let g:airline_theme='solarized'
    "let g:airline_solarized_bg='dark'
    
" use airline instead
"Plugin 'itchyny/lightline.vim'
    " Purpose:
    "   A light and configurable statusline/tabline plugin for Vim
    "   https://www.vim.org/scripts/script.php?script_id=5294
    "   https://github.com/itchyny/lightline.vim
    "   #utility
    " Usage:
    " Config:
    "let g:lightline = {
    "      \ 'colorscheme': 'wombat',
    "      \ }
    "
    "let g:lightline = {
    "      \ 'colorscheme': 'wombat',
    "      \ 'active': {
    "      \   'left': [ ['mode', 'paste'],
    "      \             ['fugitive', 'readonly', 'filename', 'modified'] ],
    "      \   'right': [ [ 'lineinfo' ], ['percent'] ]
    "      \ },
    "      \ 'component': {
    "      \   'readonly': '%{&filetype=="help"?"":&readonly?"🔒":""}',
    "      \   'modified': '%{&filetype=="help"?"":&modified?"+":&modifiable?"":"-"}',
    "      \   'fugitive': '%{exists("*fugitive#head")?fugitive#head():""}'
    "      \ },
    "      \ 'component_visible_condition': {
    "      \   'readonly': '(&filetype!="help"&& &readonly)',
    "      \   'modified': '(&filetype!="help"&&(&modified||!&modifiable))',
    "      \   'fugitive': '(exists("*fugitive#head") && ""!=fugitive#head())'
    "      \ },
    "      \ 'separator': { 'left': ' ', 'right': ' ' },
    "      \ 'subseparator': { 'left': ' ', 'right': ' ' }
    "      \ }

"vundle install error
"Plugin 'othree/vim-slumlord'
"    " Purpose:
"    " Usage:
"    " Config:

" -------------------------------------
" * VIM_Enhancement
" -------------------------------------
Plugin 'maxbrunsfeld/vim-yankstack'
    " Purpose:
    "   A lightweight implementation of emacs's kill-ring for vim
    "   https://github.com/maxbrunsfeld/vim-yankstack
    " Usage:
    " Config:
    let g:yankstack_yank_keys = ['y', 'd']
    
    nmap <c-p> <Plug>yankstack_substitute_older_paste
    nmap <c-n> <Plug>yankstack_substitute_newer_paste

Plugin 'vim-scripts/YankRing.vim'
    " Purpose:
    "   Maintains a history of previous yanks, changes and deletes
    "   https://www.vim.org/scripts/script.php?script_id=1234
    "   #utility
    " Usage:
    " Config:
    if has("win16") || has("win32") || has("win64")
        " Don't do anything
        let g:yankring_history_dir = '$VIMRUNTIME/../../../Data/settings/vimfiles/temp_dirs'
    else
        let g:yankring_history_dir = '~/dotvim/temp_dirs'
    endif

" Now replace with Vundle
"Plugin 'tpope/vim-pathogen'
"    " Purpose:
"    "   pathogen.vim: manage your runtimepath
"    "   https://www.vim.org/scripts/script.php?script_id=2332
"    " Usage:
"    " Config:
"    let s:vim_runtime = expand('<sfile>:p:h')."/.."
"    call pathogen#infect(s:vim_runtime.'/sources_forked/{}')
"    call pathogen#infect(s:vim_runtime.'/sources_non_forked/{}')
"    call pathogen#infect(s:vim_runtime.'/my_plugins/{}')
"    call pathogen#helptags()


Plugin 'vim-scripts/open-browser.vim'
    " Purpose:
    "   Open URI with your favorite browser from your favorite editor
    "   https://www.vim.org/scripts/script.php?script_id=3133
    "   https://github.com/vim-scripts/open-browser.vim
    " Usage:
    "   " In command-line
    "   :OpenBrowser http://google.com/
    "   :OpenBrowserSearch ggrks
    "   :OpenBrowserSmartSearch http://google.com/
    "   :OpenBrowserSmartSearch ggrks
    " Config:
    let g:netrw_nogx = 1 " disable netrw's gx mapping.
    
    "" Open [selected] URI under cursor.
    "nmap gx <Plug>(openbrowser-open)
    "vmap gx <Plug>(openbrowser-open)
    "
    "" Search [selected] word under cursor.
    "nmap gx <Plug>(openbrowser-search)
    "vmap gx <Plug>(openbrowser-search)
    
    " If it looks like URI, Open [selected] URI under cursor.
    " Otherwise, Search word under cursor.
    nmap gx <Plug>(openbrowser-smart-search)
    vmap gx <Plug>(openbrowser-smart-search)

Plugin 'vim-scripts/LargeFile'
    " Purpose:
    " Usage:
    " Config:


" -------------------------------------
" * ColorScheme
" -------------------------------------
Plugin 'xolox/vim-colorscheme-switcher'
    " Purpose:
    "   https://github.com/xolox/vim-colorscheme-switcher
    " Usage:
    " Config:
    "   :NextColorScheme
    "   :PrevColorScheme
    "   :RandomColorScheme
    let g:colorscheme_switcher_define_mappings = 0
    "let g:colorscheme_switcher_exclude = ['default', 'test']

Plugin 'twerth/ir_black'
    " Purpose:
    "   The original IR_Black color scheme for vim http://blog.toddwerth.com/entries/8
    "   https://github.com/twerth/ir_black

Plugin 'vim-scripts/peaksea'
    " Purpose:
    "   Refined color, contains both gui and cterm256 for dark and light background
    "   https://www.vim.org/scripts/script.php?script_id=760

Plugin 'vim-scripts/mayansmoke'
    " Purpose:
    "   Pleasant and ergonomic light-background color scheme.
    "   https://www.vim.org/scripts/script.php?script_id=3065

"Plugin 'altercation/vim-colors-solarized'
"    " Purpose:
"    "   precision colorscheme for the vim text editor
"    "   http://ethanschoonover.com/solarized
"
"Plugin 'morhetz/gruvbox'
"    " Purpose:
"    "   Retro groove color scheme for Vim
"    "   https://github.com/morhetz/gruvbox

"Plugin 'chriskempson/base16-vim'
"    " Purpose:
"    "   Base16 for Vim https://github.com/chriskempson/base16
"    "   https://github.com/chriskempson/base16-vim

Plugin 'rafi/awesome-vim-colorschemes'
    " Purpose:
    "   Collection of awesome color schemes for Neo/vim, merged for quick use.
    "   https://github.com/rafi/awesome-vim-colorschemes
    "   Scheme          Description                                             Term    GUI
    "   256noir         Dark minimal colors, to avoid distraction               v       v
    "   Abstract        Dark theme based on Abstract app                        v       v
    "   Afterglow       Adaptation from Sublime Text                            v       v
    "   Alduin          Dark rustic colors                                      v       v
    "   Anderson        Dark vim colorscheme based on colors from Wes Anderson films
    "                                                                           v       v
    "   Angr            Pleasant, mild, dark theme                              v       v
    "   Apprentice      Dark, low-contrast colorscheme                          v       v
    "   Archery         Vim colorscheme inspired by Arch Linux colors           v       v
    "   Atom            Designed to be very readable in both light and dark environments
    "                                                                                   v
    "   Carbonized      Inspired by the Carbon keycap set                       v (16)  v
    "   Challenger-deep FlatColor colorscheme                                   v       v
    "   Deep-space      Intergalactic friendly color scheme based off Hybrid    v       v
    "   Deus            For the late night coder                                v       v
    "   Dracula         Dark theme                                              v       v
    "   Focuspoint      Maintain color coordination and important keyword focus         v
    "   Flattened       Solarized, without the bullshit                         v (16)  v
    "   Github          Based on Github's syntax highlighting                   v       v
    "   Gotham          Very dark vim colorscheme                               v       v
    "   Gruvbox         Retro groove color scheme                               v       v
    "   Happy hacking   Fairly small set of colors instead of throwing rainbows at your face
    "                                                                           v       v
    "   Iceberg         Dark blue color scheme                                  v       v
    "   Papercolor      Light and Dark color schemes inspired by Google's Material Design
    "                                                                           v       v
    "   Parsec          Color scheme for people tired of solarized              v (16)  v
    "   Scheakur        A light/dark colorscheme                                v       v
    "   Hybrid          A dark colour scheme for Vim and gVim                   v       v
    "   Hybrid-material Material color scheme based on w0ng/vim-hybrid          v       v
    "   Jellybeans      Colorful, dark color scheme                             v       v
    "   Lightning       Light vim colorscheme based on Apprentice               v       v
    "   Lucid           Vivid highlights and friendly, clear colors                     v
    "   Lucius          Lucius color scheme                                     v       v
    "   Materialbox     Light and dark material palette inspired based on Gruvbox       v
    "   Meta5           Dark colorscheme, inspired by Tron                      v       v
    "   Minimalist      Darker version of material theme inspired by Sublime Text
    "                                                                           v       v
    "   Molokai         Molokai color scheme                                    v       v
    "   Molokayo        Very tweaked molokai based theme                        v       v
    "   Nord            An arctic, north-bluish clean and elegant theme         v (16)  v
    "   Oceanicnext     Oceanic Next theme                                      v       v
    "   One             Adaptation of one-light and one-dark                    v       v
    "   Onedark         Inspired by Atom's One Dark syntax theme                v       v
    "   Orbital         Dark blue base16 theme                                  v       v
    "   Paramount       Minimal colorscheme that only puts emphasis on the paramount
    "                                                                           v       v
    "   Pink-moon       Dark pastel theme                                       v       v
    "   Pyte            Clean, light (nearly white) theme                               v
    "   Rakr            Flat colorscheme light and dark variant                 v       v
    "   Rdark-terminal2 Modified rdark-terminal to enhance visibility           v
    "   Seoul256        Low-contrast color scheme based on Seoul Colors         v       v
    "   Sierra          Dark vintage colors                                     v       v
    "   Solarized8      Optimized Solarized colorschemes                        v (16)  v
    "   Space-vim-dark  Dark magenta colors                                     v       v
    "   Tender          24bit colorscheme for Vim                               v       v
    "   Termschool      Based on the "codeschool" theme, with lots of tweaks    v       v
    "   Twilight256     Imitates the Twilight theme for TextMate                v       v
    "   Two-firewatch   A blend between duotone light and firewatch (for atom)  v       v
    "   Wombat256       Wombat for 256 color xterms                             v       v

Plugin 'sjl/badwolf'
    " Purpose:
    "   A Vim color scheme. http://stevelosh.com/projects/badwolf/
    "   https://github.com/sjl/badwolf

" -------------------------------------
" * Search
" -------------------------------------
Plugin 'mileszs/ack.vim'
    " Purpose:
    "   Vim plugin for the Perl module / CLI script 'ack'
    " Usage:
    "   :help Ack
    "   :Ack [options] {pattern} [{directories}]
    "
    "   The quickfix results window is augmented with these convenience mappings:
    "
    "   ?    a quick summary of these keys, repeat to close
    "   o    to open (same as Enter)
    "   O    to open and close the quickfix window
    "   go   to preview file, open but maintain focus on ack.vim results
    "   t    to open in new tab
    "   T    to open in new tab without moving to it
    "   h    to open in horizontal split
    "   H    to open in horizontal split, keeping focus on the results
    "   v    to open in vertical split
    "   gv   to open in vertical split, keeping focus on the results
    "   q    to close the quickfix window
    " Config:

Plugin 'ctrlpvim/ctrlp.vim'
    " Purpose:
    "   Active fork of kien/ctrlp.vim
    "   Fuzzy file, buffer, mru, tag, etc finder.
    "   http://ctrlpvim.github.io/ctrlp.vim/
    "   #utility
    " Usage:
    " Config:
    let g:ctrlp_working_path_mode = 0
    
    let g:ctrlp_map = '<c-f>'
    map <leader>j :CtrlP<cr>
    map <c-b> :CtrlPBuffer<cr>
    
    let g:ctrlp_max_height = 20
    let g:ctrlp_custom_ignore = 'node_modules\|^\.DS_Store\|^\.git\|^\.coffee'

Plugin 'tpope/vim-abolish'
    " Purpose:
    "   abolish.vim: easily search for, substitute, and abbreviate multiple variants of a word
    "   https://www.vim.org/scripts/script.php?script_id=1545
    "   https://github.com/tpope/vim-abolish
    "   #utility
    " Usage:
    " Config:

" -------------------------------------
" * IDE_Related
" -------------------------------------
Plugin 'xolox/vim-shell'
    " Purpose:
    "   Improved integration between Vim and its environment (fullscreen, open URL, background command execution)
    "   http://peterodding.com/code/vim/shell/
    " Usage:
    "   <F11>           : to Fullscreen
    " Config:

Plugin 'amix/open_file_under_cursor.vim'
    " Purpose:
    "   Open file under cursor when pressing gf (if the text under the cursor is a path)
    " Usage:
    " Config:

Plugin 'scrooloose/nerdtree'
    " Purpose:
    "   A tree explorer plugin for vim.
    "   https://github.com/scrooloose/nerdtree
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
    "   Vim plugin that displays tags in a window, ordered by scope
    "   http://majutsushi.github.io/tagbar/
    " Usage:
    " Config:
    " Open and close the tagbar separately
    nmap <F5> :TagbarToggle<CR>
    "nmap <F4> :SrcExplToggle<CR>

Plugin 'vim-scripts/taglist.vim'
    " Purpose:
    "   Source code browser (supports C/C++, java, perl, python, tcl, sql, php, etc)
    "   https://www.vim.org/scripts/script.php?script_id=273
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
    "   A (G)Vim plugin for exploring the source code based on "tags", and it works like the context window of "Source Insight".
    "   https://github.com/wesleyche/SrcExpl
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
    "   official cscope_map config
    "   https://github.com/wolfpython/cscope_map.vim
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


"Plugin 'corntrace/bufexplorer'
"Plugin 'jlanzarotta/bufexplorer'
"    " Purpose:
"    "   BufExplorer Plugin for Vim
"    "   #utility
"    " Usage:
"    " Config:
"    let g:bufExplorerDefaultHelp=0
"    let g:bufExplorerShowRelativePath=1
"    let g:bufExplorerFindActive=1
"    let g:bufExplorerSortBy='name'
"    map <leader>o :BufExplorer<cr>

Plugin 'vim-scripts/winmanager'
    " Purpose:
    "   A windows style IDE for Vim 6.0
    "   https://www.vim.org/scripts/script.php?script_id=95
    "   #utility
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
" * SyntaxRelated
" -------------------------------------
"Plugin 'chr4/nginx.vim'
"    " Purpose:
"    "   Improved nginx vim plugin (incl. syntax highlighting)
"    "   nginx.vim highlights configuration files for nginx,
"    "   the high-performance web server (see http://nginx.net).
"    "   #syntax #nginx
"    " Usage:
"    " Config:

"Plugin 'sophacles/vim-bundle-mako'
"    " Purpose:
"    "   A collection of vim scripts for the mako templating engine,
"    "   in a vim bundle form (usable with pathogen.vim)
"    "   About mako: http://www.makotemplates.org/
"    "   #syntax #mako
"    " Usage:
"    " Config:

"Plugin 'groenewege/vim-less'
"    " Purpose:
"    "   vim syntax for LESS (dynamic CSS)
"    "   This vim bundle adds syntax highlighting, indenting and autocompletion
"    "   for the dynamic stylesheet language LESS.
"    "   This bundle is compatible with vim-css-color, vim-css3-syntax and
"    "   possibly other plugins that place code in after/syntax/css.vim or
"    "   after/syntax/css/*.vim.
"    "   #syntax #less #css
"    " Usage:
"    " Config:

"Plugin 'othree/xml.vim'
"    " Purpose:
"    "   helps editing xml (and [x]html, sgml, xslt) files
"    "   https://www.vim.org/scripts/script.php?script_id=1397
"    "   #ftplugin #xml
"    " Usage:
"    " Config:

"Plugin 'dpino/zencoding-vim'
"    " Purpose:
"    "   zencoding-vim is vim script support for expanding abbreviation like zen-coding(emmet).
"    "   Zen Coding — a new way of writing HTML and CSS code
"    "   #syntax #html #css
"    " Usage:
"    " Config:
"    " Enable all functions in all modes
"    let g:user_zen_mode='a'

Plugin 'fatih/vim-go'
    " Purpose:
    "   Go development plugin for Vim https://patreon.com/fatih
    "   https://github.com/fatih/vim-go-tutorial
    "   #syntax #go
    " Usage:
    " Config:
    " some shortcuts to make it easier to jump between errors in quickfix list:
    "map <C-n> :cnext<CR>
    "map <C-m> :cprevious<CR>
    "nnoremap <leader>a :cclose<CR>
    " shortcuts to build and run a Go program with <leader>b and <leader>r:
    "autocmd FileType go nmap <leader>b  <Plug>(go-build)
    "autocmd FileType go nmap <leader>r  <Plug>(go-run)
    let g:go_fmt_command = "goimports"

Plugin 'digitaltoad/vim-pug'
    " Purpose:
    "   Vim Pug (formerly Jade) template engine syntax highlighting and indention
    " Usage:
    " Config:

" -------------------------------------
" * Programming_Assist
" -------------------------------------

" Auto Complete

" plugin from http://vim-scripts.org/vim/scripts.html
Plugin 'L9'
    " Purpose:
    "   l9 is a Vim-script library, which provides some utility functions and
    "   commands for programming in Vim.
    "   https://www.vim.org/scripts/script.php?script_id=3252
    " Usage:
    " Config:

"Plugin 'vim-scripts/AutoComplPop'
Plugin 'othree/vim-autocomplpop'
    " Purpose:
    "   Automatic trigger complete popup menu
    "   https://github.com/othree/vim-autocomplpop
    " Usage:
    " Config:
    " enable auto-popup for this completion
    let g:acp_behaviorSnipmateLength = 1

Plugin 'MarcWeber/vim-addon-mw-utils'
    " Purpose:
    "   vim: interpret a file by function and cache file automatically
    " Usage:
    " Config:

Plugin 'tomtom/tlib_vim'
"Plugin 'vim-scripts/tlib'
    " Purpose:
    "   Some utility functions for VIM
    "   https://www.vim.org/scripts/script.php?script_id=1863
    " Usage:
    " Config:

Plugin 'garbas/vim-snipmate'
    " Purpose:
    "   snipMate.vim aims to be a concise vim script that implements some of
    "   TextMate's snippets features in Vim.
    "   https://www.vim.org/scripts/script.php?script_id=2540
    " Usage:
    " Config:

Plugin 'scrooloose/snipmate-snippets'
    " Purpose:
    "   A collection of snippets for snipmate
    " Usage:
    " Config:
    ino <c-j> <c-r>=snipMate#TriggerSnippet()<cr>
    snor <c-j> <esc>i<right><c-r>=snipMate#TriggerSnippet()<cr>

Plugin 'honza/vim-snippets'
    " Purpose:
    "   vim-snipmate default snippets (Previously snipmate-snippets)
    "   https://github.com/honza/vim-snippets
    " Usage:
    " Config:

Plugin 'jiangmiao/auto-pairs'
    " Purpose:
    "   Vim plugin, insert or delete brackets, parens, quotes in pair
    " Usage:
    " Config:

"Plugin 'scrooloose/syntastic'
Plugin 'vim-syntastic/syntastic'
    " Purpose:
    "   Syntax checking hacks for vim
    "   https://github.com/vim-syntastic/syntastic
    " Usage:
    " Config:

    "let g:syntasic_check_on_open = 1

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

Plugin 'vhda/verilog_systemverilog.vim'
    " Purpose:
    "   Verilog/SystemVerilog Syntax and Omni-completion
    "   https://github.com/vhda/verilog_systemverilog.vim
    " Usage:
    " Config:
        augroup syntax
        au BufNewFile,BufReadPost *.v*      so $dotvim/bundle/verilog_systemverilog.vim/syntax/verilog_systemverilog.vim
        au BufNewFile,BufReadPost *.sv*     so $dotvim/bundle/verilog_systemverilog.vim/syntax/verilog_systemverilog.vim
        au BufNewFile,BufReadPost *.h*      so $dotvim/bundle/verilog_systemverilog.vim/syntax/verilog_systemverilog.vim
        au BufNewFile,BufReadPost *.log     so $dotvim/bundle/verilog_systemverilog.vim/syntax/verilog_systemverilog.vim
        au BufNewFile,BufReadPost *.task    so $dotvim/bundle/verilog_systemverilog.vim/syntax/verilog_systemverilog.vim
        augroup END
    nmap sv :so $dotvim/bundle/verilog_systemverilog.vim/syntax/verilog_systemverilog.vim<CR>

    
Plugin 'plasticboy/vim-markdown'
    " Purpose:
    "   Markdown Vim Mode
    "   http://plasticboy.com/markdown-vim-mode/
    "   https://github.com/plasticboy/vim-markdown/
    " Usage:
    " Config:

"Plugin 'tpope/vim-markdown'
"    " Purpose:
"    "   Vim Markdown runtime files
"    "   https://github.com/tpope/vim-markdown
"    " Usage:
"    " Config:

Plugin 'hdima/python-syntax'
    " Purpose:
    "   Python syntax highlighting script for Vim
    "   https://www.vim.org/scripts/script.php?script_id=790
    "   https://github.com/hdima/python-syntax
    "   #syntax #vim
    " Usage:
    " Config:

Plugin 'nvie/vim-flake8'
    " Purpose:
    "   Flake8 plugin for Vim
    "   https://github.com/nvie/vim-flake8
    "   vim-flake8 is a Vim plugin that runs the currently open file through
    "   Flake8, a static syntax and style checker for Python source code. It
    "   supersedes both vim-pyflakes and vim-pep8.
    "   #utility #python #flake8
    " Usage:
    "   1. Open a Python file
    "   2. Press <F7> to run flake8 on it
    " Config:
    "autocmd FileType python map <buffer> <F3> :call Flake8()<CR>

Plugin 'vim-scripts/Pydiction'
    " Purpose:
    "   Tab-complete your Python code
    "   https://www.vim.org/scripts/script.php?script_id=850
    "   https://github.com/vim-scripts/Pydiction
    "   #utility #python
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
    " Purpose:
    "   Updated javacomplete plugin for vim.
    "   https://github.com/artur-shaik/vim-javacomplete2
    "   #utility #java
    " Usage:
    " Config:

"Plugin 'kchmck/vim-coffee-script'
"    " Purpose:
"    "   CoffeeScript support for vim
"    "   https://github.com/kchmck/vim-coffee-script
"    " Usage:
"    " Config:

"Plugin 'aklt/plantuml-syntax'
"    " Purpose:
"    "   vim syntax file for plantuml
"    "   https://github.com/aklt/plantuml-syntax
"    " Usage:
"    " Config:


Plugin 'ntpeters/vim-better-whitespace'
    " Purpose:
    "   Better whitespace highlighting for Vim
    "   https://github.com/ntpeters/vim-better-whitespace
    " Usage:
    " Config:
    "To ignore lines that contain only whitespace
    let g:better_whitespace_skip_empty_lines=1



" -------------------------------------
" * Utility
" -------------------------------------
Plugin 'itchyny/calendar.vim'
    " Purpose:
    "   A calendar application for Vim
    "   https://github.com/itchyny/calendar.vim
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
    "   Personal Wiki for Vim
    "   http://vimwiki.github.io/
    "   https://github.com/vimwiki/vimwiki
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

    
Plugin 'jceb/vim-orgmode'
    " Purpose:
    "   Text outlining and task management for Vim based on Emacs' Org-Mode
    "   https://github.com/jceb/vim-orgmode
    " Usage:
    " Config:
