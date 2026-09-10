=== nixie_sat::trail::propagation::PropagationQueue::append ===

/dev/shm/nixie-whole-list-moves-target/perf/examples/stats_solve:     file format elf64-x86-64


Disassembly of section .text:

0000000000064250 <nixie_sat::trail::propagation::PropagationQueue::append>:
   64250:	89 f0                	mov    eax,esi
   64252:	24 01                	and    al,0x1
   64254:	89 f1                	mov    ecx,esi
   64256:	d1 e9                	shr    ecx,1
   64258:	44 8b 47 38          	mov    r8d,DWORD PTR [rdi+0x38]
   6425c:	4c 8b 4f 10          	mov    r9,QWORD PTR [rdi+0x10]
   64260:	4c 8b 57 28          	mov    r10,QWORD PTR [rdi+0x28]
   64264:	48 8d 0c 89          	lea    rcx,[rcx+rcx*4]
   64268:	41 c7 04 89 01 00 00 	mov    DWORD PTR [r9+rcx*4],0x1
   6426f:	00
   64270:	41 89 54 89 04       	mov    DWORD PTR [r9+rcx*4+0x4],edx
   64275:	45 89 44 89 08       	mov    DWORD PTR [r9+rcx*4+0x8],r8d
   6427a:	45 89 54 89 0c       	mov    DWORD PTR [r9+rcx*4+0xc],r10d
   6427f:	41 88 44 89 10       	mov    BYTE PTR [r9+rcx*4+0x10],al
   64284:	48 8b 47 20          	mov    rax,QWORD PTR [rdi+0x20]
   64288:	42 89 34 90          	mov    DWORD PTR [rax+r10*4],esi
   6428c:	49 ff c2             	inc    r10
   6428f:	4c 89 57 28          	mov    QWORD PTR [rdi+0x28],r10
   64293:	c3                   	ret
=== nixie_sat::solver::propagate::list_kernel::scan ===

/dev/shm/nixie-whole-list-moves-target/perf/examples/stats_solve:     file format elf64-x86-64


Disassembly of section .text:

0000000000064df0 <nixie_sat::solver::propagate::list_kernel::scan>:
   64df0:	55                   	push   rbp
   64df1:	41 57                	push   r15
   64df3:	41 56                	push   r14
   64df5:	41 55                	push   r13
   64df7:	41 54                	push   r12
   64df9:	53                   	push   rbx
   64dfa:	48 83 ec 28          	sub    rsp,0x28
   64dfe:	4c 8b 7c 24 78       	mov    r15,QWORD PTR [rsp+0x78]
   64e03:	48 8b 5c 24 70       	mov    rbx,QWORD PTR [rsp+0x70]
   64e08:	48 39 d6             	cmp    rsi,rdx
   64e0b:	0f 84 22 01 00 00    	je     64f33 <nixie_sat::solver::propagate::list_kernel::scan+0x143>
   64e11:	4c 8b 6c 24 68       	mov    r13,QWORD PTR [rsp+0x68]
   64e16:	eb 15                	jmp    64e2d <nixie_sat::solver::propagate::list_kernel::scan+0x3d>
   64e18:	0f 1f 84 00 00 00 00 	nop    DWORD PTR [rax+rax*1+0x0]
   64e1f:	00
   64e20:	44 89 70 04          	mov    DWORD PTR [rax+0x4],r14d
   64e24:	48 39 d6             	cmp    rsi,rdx
   64e27:	0f 84 06 01 00 00    	je     64f33 <nixie_sat::solver::propagate::list_kernel::scan+0x143>
   64e2d:	48 89 f0             	mov    rax,rsi
   64e30:	44 8b 56 04          	mov    r10d,DWORD PTR [rsi+0x4]
   64e34:	48 83 c6 08          	add    rsi,0x8
   64e38:	43 80 3c 10 00       	cmp    BYTE PTR [r8+r10*1],0x0
   64e3d:	7f e5                	jg     64e24 <nixie_sat::solver::propagate::list_kernel::scan+0x34>
   64e3f:	44 8b 10             	mov    r10d,DWORD PTR [rax]
   64e42:	41 83 fa ff          	cmp    r10d,0xffffffff
   64e46:	0f 84 65 01 00 00    	je     64fb1 <nixie_sat::solver::propagate::list_kernel::scan+0x1c1>
   64e4c:	43 f6 44 15 06 01    	test   BYTE PTR [r13+r10*1+0x6],0x1
   64e52:	0f 85 59 01 00 00    	jne    64fb1 <nixie_sat::solver::propagate::list_kernel::scan+0x1c1>
   64e58:	43 8b 6c 15 00       	mov    ebp,DWORD PTR [r13+r10*1+0x0]
   64e5d:	48 83 fd 01          	cmp    rbp,0x1
   64e61:	0f 86 ba 01 00 00    	jbe    65021 <nixie_sat::solver::propagate::list_kernel::scan+0x231>
   64e67:	47 8b 74 15 0c       	mov    r14d,DWORD PTR [r13+r10*1+0xc]
   64e6c:	47 33 74 15 10       	xor    r14d,DWORD PTR [r13+r10*1+0x10]
   64e71:	41 31 ce             	xor    r14d,ecx
   64e74:	47 89 74 15 0c       	mov    DWORD PTR [r13+r10*1+0xc],r14d
   64e79:	43 89 4c 15 10       	mov    DWORD PTR [r13+r10*1+0x10],ecx
   64e7e:	47 0f b6 1c 30       	movzx  r11d,BYTE PTR [r8+r14*1]
   64e83:	45 84 db             	test   r11b,r11b
   64e86:	7f 98                	jg     64e20 <nixie_sat::solver::propagate::list_kernel::scan+0x30>
   64e88:	49 8d 5d 10          	lea    rbx,[r13+0x10]
   64e8c:	4c 01 d3             	add    rbx,r10
   64e8f:	48 8d 2c ad f8 ff ff 	lea    rbp,[rbp*4-0x8]
   64e96:	ff
   64e97:	66 0f 1f 84 00 00 00 	nop    WORD PTR [rax+rax*1+0x0]
   64e9e:	00 00
   64ea0:	48 85 ed             	test   rbp,rbp
   64ea3:	74 20                	je     64ec5 <nixie_sat::solver::propagate::list_kernel::scan+0xd5>
   64ea5:	44 8b 7b 04          	mov    r15d,DWORD PTR [rbx+0x4]
   64ea9:	47 0f b6 24 38       	movzx  r12d,BYTE PTR [r8+r15*1]
   64eae:	45 84 e4             	test   r12b,r12b
   64eb1:	7f 6d                	jg     64f20 <nixie_sat::solver::propagate::list_kernel::scan+0x130>
   64eb3:	48 83 c3 04          	add    rbx,0x4
   64eb7:	48 83 c5 fc          	add    rbp,0xfffffffffffffffc
   64ebb:	45 84 e4             	test   r12b,r12b
   64ebe:	75 e0                	jne    64ea0 <nixie_sat::solver::propagate::list_kernel::scan+0xb0>
   64ec0:	e9 9a 00 00 00       	jmp    64f5f <nixie_sat::solver::propagate::list_kernel::scan+0x16f>
   64ec5:	44 89 70 04          	mov    DWORD PTR [rax+0x4],r14d
   64ec9:	43 8b 44 15 08       	mov    eax,DWORD PTR [r13+r10*1+0x8]
   64ece:	45 84 db             	test   r11b,r11b
   64ed1:	0f 88 1b 01 00 00    	js     64ff2 <nixie_sat::solver::propagate::list_kernel::scan+0x202>
   64ed7:	48 89 7c 24 20       	mov    QWORD PTR [rsp+0x20],rdi
   64edc:	48 8b 7c 24 60       	mov    rdi,QWORD PTR [rsp+0x60]
   64ee1:	48 89 74 24 18       	mov    QWORD PTR [rsp+0x18],rsi
   64ee6:	44 89 f6             	mov    esi,r14d
   64ee9:	49 89 d4             	mov    r12,rdx
   64eec:	89 c2                	mov    edx,eax
   64eee:	4c 89 cb             	mov    rbx,r9
   64ef1:	4d 89 c7             	mov    r15,r8
   64ef4:	89 cd                	mov    ebp,ecx
   64ef6:	e8 55 f3 ff ff       	call   64250 <nixie_sat::trail::propagation::PropagationQueue::append>
   64efb:	48 8b 74 24 18       	mov    rsi,QWORD PTR [rsp+0x18]
   64f00:	89 e9                	mov    ecx,ebp
   64f02:	4d 89 f8             	mov    r8,r15
   64f05:	4c 89 e2             	mov    rdx,r12
   64f08:	49 89 d9             	mov    r9,rbx
   64f0b:	48 8b 7c 24 20       	mov    rdi,QWORD PTR [rsp+0x20]
   64f10:	43 c6 04 37 01       	mov    BYTE PTR [r15+r14*1],0x1
   64f15:	49 83 f6 01          	xor    r14,0x1
   64f19:	43 c6 04 37 ff       	mov    BYTE PTR [r15+r14*1],0xff
   64f1e:	eb 04                	jmp    64f24 <nixie_sat::solver::propagate::list_kernel::scan+0x134>
   64f20:	44 89 78 04          	mov    DWORD PTR [rax+0x4],r15d
   64f24:	48 8b 5c 24 70       	mov    rbx,QWORD PTR [rsp+0x70]
   64f29:	4c 8b 7c 24 78       	mov    r15,QWORD PTR [rsp+0x78]
   64f2e:	e9 f1 fe ff ff       	jmp    64e24 <nixie_sat::solver::propagate::list_kernel::scan+0x34>
   64f33:	49 29 df             	sub    r15,rbx
   64f36:	49 c1 ff 02          	sar    r15,0x2
   64f3a:	48 b8 ab aa aa aa aa 	movabs rax,0xaaaaaaaaaaaaaaab
   64f41:	aa aa aa
   64f44:	49 0f af c7          	imul   rax,r15
   64f48:	48 89 57 10          	mov    QWORD PTR [rdi+0x10],rdx
   64f4c:	c7 47 18 ff ff ff ff 	mov    DWORD PTR [rdi+0x18],0xffffffff
   64f53:	48 89 1f             	mov    QWORD PTR [rdi],rbx
   64f56:	48 89 47 08          	mov    QWORD PTR [rdi+0x8],rax
   64f5a:	e9 84 00 00 00       	jmp    64fe3 <nixie_sat::solver::propagate::list_kernel::scan+0x1f3>
   64f5f:	47 89 7c 15 10       	mov    DWORD PTR [r13+r10*1+0x10],r15d
   64f64:	89 0b                	mov    DWORD PTR [rbx],ecx
   64f66:	47 8b 5c 15 10       	mov    r11d,DWORD PTR [r13+r10*1+0x10]
   64f6b:	41 83 f3 01          	xor    r11d,0x1
   64f6f:	48 8b 5c 24 78       	mov    rbx,QWORD PTR [rsp+0x78]
   64f74:	44 89 13             	mov    DWORD PTR [rbx],r10d
   64f77:	44 89 73 04          	mov    DWORD PTR [rbx+0x4],r14d
   64f7b:	44 89 5b 08          	mov    DWORD PTR [rbx+0x8],r11d
   64f7f:	48 83 c3 0c          	add    rbx,0xc
   64f83:	48 89 34 24          	mov    QWORD PTR [rsp],rsi
   64f87:	48 89 44 24 08       	mov    QWORD PTR [rsp+0x8],rax
   64f8c:	48 89 54 24 10       	mov    QWORD PTR [rsp+0x10],rdx
   64f91:	48 83 ec 08          	sub    rsp,0x8
   64f95:	48 8d 74 24 08       	lea    rsi,[rsp+0x8]
   64f9a:	89 ca                	mov    edx,ecx
   64f9c:	4c 89 c1             	mov    rcx,r8
   64f9f:	4d 89 c8             	mov    r8,r9
   64fa2:	4c 8b 4c 24 68       	mov    r9,QWORD PTR [rsp+0x68]
   64fa7:	53                   	push   rbx
   64fa8:	ff b4 24 80 00 00 00 	push   QWORD PTR [rsp+0x80]
   64faf:	eb 27                	jmp    64fd8 <nixie_sat::solver::propagate::list_kernel::scan+0x1e8>
   64fb1:	48 89 34 24          	mov    QWORD PTR [rsp],rsi
   64fb5:	48 89 44 24 08       	mov    QWORD PTR [rsp+0x8],rax
   64fba:	48 89 54 24 10       	mov    QWORD PTR [rsp+0x10],rdx
   64fbf:	48 83 ec 08          	sub    rsp,0x8
   64fc3:	48 8d 74 24 08       	lea    rsi,[rsp+0x8]
   64fc8:	89 ca                	mov    edx,ecx
   64fca:	4c 89 c1             	mov    rcx,r8
   64fcd:	4d 89 c8             	mov    r8,r9
   64fd0:	4c 8b 4c 24 68       	mov    r9,QWORD PTR [rsp+0x68]
   64fd5:	41 57                	push   r15
   64fd7:	53                   	push   rbx
   64fd8:	41 55                	push   r13
   64fda:	e8 11 01 00 00       	call   650f0 <nixie_sat::solver::propagate::list_kernel::scan>
   64fdf:	48 83 c4 20          	add    rsp,0x20
   64fe3:	48 83 c4 28          	add    rsp,0x28
   64fe7:	5b                   	pop    rbx
   64fe8:	41 5c                	pop    r12
   64fea:	41 5d                	pop    r13
   64fec:	41 5e                	pop    r14
   64fee:	41 5f                	pop    r15
   64ff0:	5d                   	pop    rbp
   64ff1:	c3                   	ret
   64ff2:	48 8b 74 24 70       	mov    rsi,QWORD PTR [rsp+0x70]
   64ff7:	4c 8b 44 24 78       	mov    r8,QWORD PTR [rsp+0x78]
   64ffc:	49 29 f0             	sub    r8,rsi
   64fff:	49 c1 f8 02          	sar    r8,0x2
   65003:	48 b9 ab aa aa aa aa 	movabs rcx,0xaaaaaaaaaaaaaaab
   6500a:	aa aa aa
   6500d:	49 0f af c8          	imul   rcx,r8
   65011:	48 89 57 10          	mov    QWORD PTR [rdi+0x10],rdx
   65015:	89 47 18             	mov    DWORD PTR [rdi+0x18],eax
   65018:	48 89 37             	mov    QWORD PTR [rdi],rsi
   6501b:	48 89 4f 08          	mov    QWORD PTR [rdi+0x8],rcx
   6501f:	eb c2                	jmp    64fe3 <nixie_sat::solver::propagate::list_kernel::scan+0x1f3>
   65021:	48 8d 3d 60 e0 fa ff 	lea    rdi,[rip+0xfffffffffffae060]        # 13088 <core::num::imp::flt2dec::strategy::dragon::POW5TO256+0x171c>
   65028:	48 8d 15 31 b1 0b 00 	lea    rdx,[rip+0xbb131]        # 120160 <__frame_dummy_init_array_entry+0x5260>
   6502f:	be 13 00 00 00       	mov    esi,0x13
   65034:	e8 87 64 fd ff       	call   3b4c0 <core::panicking::panic_fmt>
=== nixie_sat::solver::propagate::list_kernel::scan ===

/dev/shm/nixie-whole-list-moves-target/perf/examples/stats_solve:     file format elf64-x86-64


Disassembly of section .text:

00000000000650f0 <nixie_sat::solver::propagate::list_kernel::scan>:
   650f0:	55                   	push   rbp
   650f1:	41 57                	push   r15
   650f3:	41 56                	push   r14
   650f5:	41 55                	push   r13
   650f7:	41 54                	push   r12
   650f9:	53                   	push   rbx
   650fa:	48 83 ec 28          	sub    rsp,0x28
   650fe:	4c 89 4c 24 18       	mov    QWORD PTR [rsp+0x18],r9
   65103:	48 89 7c 24 08       	mov    QWORD PTR [rsp+0x8],rdi
   65108:	48 8b 44 24 70       	mov    rax,QWORD PTR [rsp+0x70]
   6510d:	48 89 04 24          	mov    QWORD PTR [rsp],rax
   65111:	4c 8b 26             	mov    r12,QWORD PTR [rsi]
   65114:	4c 8b 7e 08          	mov    r15,QWORD PTR [rsi+0x8]
   65118:	48 8b 7e 10          	mov    rdi,QWORD PTR [rsi+0x10]
   6511c:	49 39 fc             	cmp    r12,rdi
   6511f:	0f 84 62 01 00 00    	je     65287 <nixie_sat::solver::propagate::list_kernel::scan+0x197>
   65125:	48 89 cd             	mov    rbp,rcx
   65128:	41 89 d0             	mov    r8d,edx
   6512b:	4c 8b 74 24 60       	mov    r14,QWORD PTR [rsp+0x60]
   65130:	4d 8d 4e 10          	lea    r9,[r14+0x10]
   65134:	48 89 7c 24 10       	mov    QWORD PTR [rsp+0x10],rdi
   65139:	eb 19                	jmp    65154 <nixie_sat::solver::propagate::list_kernel::scan+0x64>
   6513b:	0f 1f 44 00 00       	nop    DWORD PTR [rax+rax*1+0x0]
   65140:	41 89 1f             	mov    DWORD PTR [r15],ebx
   65143:	41 89 57 04          	mov    DWORD PTR [r15+0x4],edx
   65147:	49 83 c7 08          	add    r15,0x8
   6514b:	49 39 fc             	cmp    r12,rdi
   6514e:	0f 84 33 01 00 00    	je     65287 <nixie_sat::solver::propagate::list_kernel::scan+0x197>
   65154:	41 8b 1c 24          	mov    ebx,DWORD PTR [r12]
   65158:	41 8b 44 24 04       	mov    eax,DWORD PTR [r12+0x4]
   6515d:	49 83 c4 08          	add    r12,0x8
   65161:	80 7c 05 00 00       	cmp    BYTE PTR [rbp+rax*1+0x0],0x0
   65166:	0f 8f 03 01 00 00    	jg     6526f <nixie_sat::solver::propagate::list_kernel::scan+0x17f>
   6516c:	83 fb ff             	cmp    ebx,0xffffffff
   6516f:	74 da                	je     6514b <nixie_sat::solver::propagate::list_kernel::scan+0x5b>
   65171:	41 f6 44 1e 06 01    	test   BYTE PTR [r14+rbx*1+0x6],0x1
   65177:	75 d2                	jne    6514b <nixie_sat::solver::propagate::list_kernel::scan+0x5b>
   65179:	41 8b 0c 1e          	mov    ecx,DWORD PTR [r14+rbx*1]
   6517d:	48 83 f9 01          	cmp    rcx,0x1
   65181:	0f 86 7c 01 00 00    	jbe    65303 <nixie_sat::solver::propagate::list_kernel::scan+0x213>
   65187:	45 8b 6c 1e 0c       	mov    r13d,DWORD PTR [r14+rbx*1+0xc]
   6518c:	45 33 6c 1e 10       	xor    r13d,DWORD PTR [r14+rbx*1+0x10]
   65191:	45 31 c5             	xor    r13d,r8d
   65194:	45 89 6c 1e 0c       	mov    DWORD PTR [r14+rbx*1+0xc],r13d
   65199:	45 89 44 1e 10       	mov    DWORD PTR [r14+rbx*1+0x10],r8d
   6519e:	42 80 7c 2d 00 00    	cmp    BYTE PTR [rbp+r13*1+0x0],0x0
   651a4:	0f 8f d1 00 00 00    	jg     6527b <nixie_sat::solver::propagate::list_kernel::scan+0x18b>
   651aa:	49 8d 04 19          	lea    rax,[r9+rbx*1]
   651ae:	48 8d 0c 8d f8 ff ff 	lea    rcx,[rcx*4-0x8]
   651b5:	ff
   651b6:	66 2e 0f 1f 84 00 00 	cs nop WORD PTR [rax+rax*1+0x0]
   651bd:	00 00 00
   651c0:	48 85 c9             	test   rcx,rcx
   651c3:	74 4b                	je     65210 <nixie_sat::solver::propagate::list_kernel::scan+0x120>
   651c5:	8b 50 04             	mov    edx,DWORD PTR [rax+0x4]
   651c8:	0f b6 74 15 00       	movzx  esi,BYTE PTR [rbp+rdx*1+0x0]
   651cd:	40 84 f6             	test   sil,sil
   651d0:	0f 8f 6a ff ff ff    	jg     65140 <nixie_sat::solver::propagate::list_kernel::scan+0x50>
   651d6:	48 83 c0 04          	add    rax,0x4
   651da:	48 83 c1 fc          	add    rcx,0xfffffffffffffffc
   651de:	40 84 f6             	test   sil,sil
   651e1:	75 dd                	jne    651c0 <nixie_sat::solver::propagate::list_kernel::scan+0xd0>
   651e3:	41 89 54 1e 10       	mov    DWORD PTR [r14+rbx*1+0x10],edx
   651e8:	44 89 00             	mov    DWORD PTR [rax],r8d
   651eb:	41 8b 44 1e 10       	mov    eax,DWORD PTR [r14+rbx*1+0x10]
   651f0:	83 f0 01             	xor    eax,0x1
   651f3:	48 8b 0c 24          	mov    rcx,QWORD PTR [rsp]
   651f7:	89 19                	mov    DWORD PTR [rcx],ebx
   651f9:	44 89 69 04          	mov    DWORD PTR [rcx+0x4],r13d
   651fd:	89 41 08             	mov    DWORD PTR [rcx+0x8],eax
   65200:	48 83 c1 0c          	add    rcx,0xc
   65204:	48 89 0c 24          	mov    QWORD PTR [rsp],rcx
   65208:	e9 3e ff ff ff       	jmp    6514b <nixie_sat::solver::propagate::list_kernel::scan+0x5b>
   6520d:	0f 1f 00             	nop    DWORD PTR [rax]
   65210:	41 89 1f             	mov    DWORD PTR [r15],ebx
   65213:	45 89 6f 04          	mov    DWORD PTR [r15+0x4],r13d
   65217:	49 83 c7 08          	add    r15,0x8
   6521b:	42 80 7c 2d 00 00    	cmp    BYTE PTR [rbp+r13*1+0x0],0x0
   65221:	0f 88 bd 00 00 00    	js     652e4 <nixie_sat::solver::propagate::list_kernel::scan+0x1f4>
   65227:	41 8b 54 1e 08       	mov    edx,DWORD PTR [r14+rbx*1+0x8]
   6522c:	48 8b 7c 24 18       	mov    rdi,QWORD PTR [rsp+0x18]
   65231:	44 89 ee             	mov    esi,r13d
   65234:	4c 89 7c 24 20       	mov    QWORD PTR [rsp+0x20],r15
   65239:	4d 89 f7             	mov    r15,r14
   6523c:	45 89 c6             	mov    r14d,r8d
   6523f:	4c 89 cb             	mov    rbx,r9
   65242:	e8 09 f0 ff ff       	call   64250 <nixie_sat::trail::propagation::PropagationQueue::append>
   65247:	49 89 d9             	mov    r9,rbx
   6524a:	45 89 f0             	mov    r8d,r14d
   6524d:	4d 89 fe             	mov    r14,r15
   65250:	4c 8b 7c 24 20       	mov    r15,QWORD PTR [rsp+0x20]
   65255:	48 8b 7c 24 10       	mov    rdi,QWORD PTR [rsp+0x10]
   6525a:	42 c6 44 2d 00 01    	mov    BYTE PTR [rbp+r13*1+0x0],0x1
   65260:	49 83 f5 01          	xor    r13,0x1
   65264:	42 c6 44 2d 00 ff    	mov    BYTE PTR [rbp+r13*1+0x0],0xff
   6526a:	e9 dc fe ff ff       	jmp    6514b <nixie_sat::solver::propagate::list_kernel::scan+0x5b>
   6526f:	41 89 1f             	mov    DWORD PTR [r15],ebx
   65272:	41 89 47 04          	mov    DWORD PTR [r15+0x4],eax
   65276:	e9 cc fe ff ff       	jmp    65147 <nixie_sat::solver::propagate::list_kernel::scan+0x57>
   6527b:	41 89 1f             	mov    DWORD PTR [r15],ebx
   6527e:	45 89 6f 04          	mov    DWORD PTR [r15+0x4],r13d
   65282:	e9 c0 fe ff ff       	jmp    65147 <nixie_sat::solver::propagate::list_kernel::scan+0x57>
   65287:	4c 29 e7             	sub    rdi,r12
   6528a:	49 89 fd             	mov    r13,rdi
   6528d:	4c 89 ff             	mov    rdi,r15
   65290:	4c 89 e6             	mov    rsi,r12
   65293:	4c 89 ea             	mov    rdx,r13
   65296:	ff 15 04 c6 0b 00    	call   QWORD PTR [rip+0xbc604]        # 1218a0 <memmove@GLIBC_2.2.5>
   6529c:	4d 01 fd             	add    r13,r15
   6529f:	b8 ff ff ff ff       	mov    eax,0xffffffff
   652a4:	48 8b 4c 24 68       	mov    rcx,QWORD PTR [rsp+0x68]
   652a9:	48 8b 34 24          	mov    rsi,QWORD PTR [rsp]
   652ad:	48 29 ce             	sub    rsi,rcx
   652b0:	48 c1 fe 02          	sar    rsi,0x2
   652b4:	48 ba ab aa aa aa aa 	movabs rdx,0xaaaaaaaaaaaaaaab
   652bb:	aa aa aa
   652be:	48 0f af d6          	imul   rdx,rsi
   652c2:	48 8b 74 24 08       	mov    rsi,QWORD PTR [rsp+0x8]
   652c7:	4c 89 6e 10          	mov    QWORD PTR [rsi+0x10],r13
   652cb:	89 46 18             	mov    DWORD PTR [rsi+0x18],eax
   652ce:	48 89 0e             	mov    QWORD PTR [rsi],rcx
   652d1:	48 89 56 08          	mov    QWORD PTR [rsi+0x8],rdx
   652d5:	48 83 c4 28          	add    rsp,0x28
   652d9:	5b                   	pop    rbx
   652da:	41 5c                	pop    r12
   652dc:	41 5d                	pop    r13
   652de:	41 5e                	pop    r14
   652e0:	41 5f                	pop    r15
   652e2:	5d                   	pop    rbp
   652e3:	c3                   	ret
   652e4:	4c 29 e7             	sub    rdi,r12
   652e7:	49 89 fd             	mov    r13,rdi
   652ea:	4c 89 ff             	mov    rdi,r15
   652ed:	4c 89 e6             	mov    rsi,r12
   652f0:	4c 89 ea             	mov    rdx,r13
   652f3:	ff 15 a7 c5 0b 00    	call   QWORD PTR [rip+0xbc5a7]        # 1218a0 <memmove@GLIBC_2.2.5>
   652f9:	4d 01 fd             	add    r13,r15
   652fc:	41 8b 44 1e 08       	mov    eax,DWORD PTR [r14+rbx*1+0x8]
   65301:	eb a1                	jmp    652a4 <nixie_sat::solver::propagate::list_kernel::scan+0x1b4>
   65303:	48 8d 3d 7e dd fa ff 	lea    rdi,[rip+0xfffffffffffadd7e]        # 13088 <core::num::imp::flt2dec::strategy::dragon::POW5TO256+0x171c>
   6530a:	48 8d 15 4f ae 0b 00 	lea    rdx,[rip+0xbae4f]        # 120160 <__frame_dummy_init_array_entry+0x5260>
   65311:	be 13 00 00 00       	mov    esi,0x13
   65316:	e8 a5 61 fd ff       	call   3b4c0 <core::panicking::panic_fmt>
=== nixie_sat::watched::moves::Moves::flush ===

/dev/shm/nixie-whole-list-moves-target/perf/examples/stats_solve:     file format elf64-x86-64


Disassembly of section .text:

0000000000065040 <nixie_sat::watched::moves::Moves::flush>:
   65040:	55                   	push   rbp
   65041:	41 57                	push   r15
   65043:	41 56                	push   r14
   65045:	41 55                	push   r13
   65047:	41 54                	push   r12
   65049:	53                   	push   rbx
   6504a:	48 83 ec 28          	sub    rsp,0x28
   6504e:	49 89 d6             	mov    r14,rdx
   65051:	49 89 ff             	mov    r15,rdi
   65054:	48 c1 e6 02          	shl    rsi,0x2
   65058:	4c 8d 2c 76          	lea    r13,[rsi+rsi*2]
   6505c:	31 ed                	xor    ebp,ebp
   6505e:	48 89 4c 24 08       	mov    QWORD PTR [rsp+0x8],rcx
   65063:	eb 25                	jmp    6508a <nixie_sat::watched::moves::Moves::flush+0x4a>
   65065:	66 66 2e 0f 1f 84 00 	data16 cs nop WORD PTR [rax+rax*1+0x0]
   6506c:	00 00 00 00
   65070:	49 8b 44 24 08       	mov    rax,QWORD PTR [r12+0x8]
   65075:	0f 13 04 d8          	movlps QWORD PTR [rax+rbx*8],xmm0
   65079:	48 ff c3             	inc    rbx
   6507c:	49 89 5c 24 10       	mov    QWORD PTR [r12+0x10],rbx
   65081:	48 83 c5 0c          	add    rbp,0xc
   65085:	49 39 ed             	cmp    r13,rbp
   65088:	74 3c                	je     650c6 <nixie_sat::watched::moves::Moves::flush+0x86>
   6508a:	41 8b 7c 2f 08       	mov    edi,DWORD PTR [r15+rbp*1+0x8]
   6508f:	48 39 f9             	cmp    rcx,rdi
   65092:	76 41                	jbe    650d5 <nixie_sat::watched::moves::Moves::flush+0x95>
   65094:	48 8d 04 7f          	lea    rax,[rdi+rdi*2]
   65098:	4d 8d 24 c6          	lea    r12,[r14+rax*8]
   6509c:	f2 41 0f 10 04 2f    	movsd  xmm0,QWORD PTR [r15+rbp*1]
   650a2:	49 8b 5c c6 10       	mov    rbx,QWORD PTR [r14+rax*8+0x10]
   650a7:	49 3b 1c c6          	cmp    rbx,QWORD PTR [r14+rax*8]
   650ab:	75 c3                	jne    65070 <nixie_sat::watched::moves::Moves::flush+0x30>
   650ad:	4c 89 e7             	mov    rdi,r12
   650b0:	0f 29 44 24 10       	movaps XMMWORD PTR [rsp+0x10],xmm0
   650b5:	e8 56 0e ff ff       	call   55f10 <alloc::raw_vec::RawVec<T,A>::grow_one>
   650ba:	0f 28 44 24 10       	movaps xmm0,XMMWORD PTR [rsp+0x10]
   650bf:	48 8b 4c 24 08       	mov    rcx,QWORD PTR [rsp+0x8]
   650c4:	eb aa                	jmp    65070 <nixie_sat::watched::moves::Moves::flush+0x30>
   650c6:	48 83 c4 28          	add    rsp,0x28
   650ca:	5b                   	pop    rbx
   650cb:	41 5c                	pop    r12
   650cd:	41 5d                	pop    r13
   650cf:	41 5e                	pop    r14
   650d1:	41 5f                	pop    r15
   650d3:	5d                   	pop    rbp
   650d4:	c3                   	ret
   650d5:	48 8d 15 4c b2 0b 00 	lea    rdx,[rip+0xbb24c]        # 120328 <__frame_dummy_init_array_entry+0x5428>
   650dc:	48 89 ce             	mov    rsi,rcx
   650df:	e8 93 81 fd ff       	call   3d277 <core::panicking::panic_bounds_check>
