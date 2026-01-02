autocmd Filetype h setlocal tabstop=2 shiftwidth=2 softtabstop=2
autocmd Filetype hpp setlocal tabstop=2 shiftwidth=2 softtabstop=2
autocmd Filetype c setlocal tabstop=2 shiftwidth=2 softtabstop=2
autocmd Filetype cpp setlocal tabstop=2 shiftwidth=2 softtabstop=2
set shiftwidth=2
setlocal shiftwidth=2
nnoremap cc :e %:p:s,.h$,.X123X,:s,.cpp$,.h,:s,.X123X$,.cpp,<CR>
