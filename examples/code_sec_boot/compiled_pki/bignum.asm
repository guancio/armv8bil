
secure_bios.bignum.o:     file format elf64-littleaarch64


Disassembly of section .keywords:

0000000000000000 <secure_bios_bignum_header>:
   0:	61654824 	.word	0x61654824
   4:	4c525564 	.word	0x4c525564
   8:	7468203a 	.word	0x7468203a
   c:	3a737074 	.word	0x3a737074
  10:	6d632f2f 	.word	0x6d632f2f
  14:	7478652d 	.word	0x7478652d
  18:	7665642e 	.word	0x7665642e
  1c:	696e6f2e 	.word	0x696e6f2e
  20:	2e6f6574 	.word	0x2e6f6574
  24:	2f6d6f63 	.word	0x2f6d6f63
  28:	2f6e7673 	.word	0x2f6e7673
  2c:	6f6e616e 	.word	0x6f6e616e
  30:	2f766564 	.word	0x2f766564
  34:	6b636170 	.word	0x6b636170
  38:	73656761 	.word	0x73656761
  3c:	6365732f 	.word	0x6365732f
  40:	5f657275 	.word	0x5f657275
  44:	736f6962 	.word	0x736f6962
  48:	6172622f 	.word	0x6172622f
  4c:	6568636e 	.word	0x6568636e
  50:	61682f73 	.word	0x61682f73
  54:	636f7073 	.word	0x636f7073
  58:	6b69682f 	.word	0x6b69682f
  5c:	732f7965 	.word	0x732f7965
  60:	72756365 	.word	0x72756365
  64:	69625f65 	.word	0x69625f65
  68:	702f736f 	.word	0x702f736f
  6c:	622f696b 	.word	0x622f696b
  70:	756e6769 	.word	0x756e6769
  74:	20682e6d 	.word	0x20682e6d
  78:	52242024 	.word	0x52242024
  7c:	73697665 	.word	0x73697665
  80:	3a6e6f69 	.word	0x3a6e6f69
  84:	34373120 	.word	0x34373120
  88:	24203131 	.word	0x24203131
  8c:	00000000 	.word	0x00000000

0000000000000090 <secure_bios_bignum_code>:
  90:	61654824 	.word	0x61654824
  94:	4c525564 	.word	0x4c525564
  98:	7468203a 	.word	0x7468203a
  9c:	3a737074 	.word	0x3a737074
  a0:	6d632f2f 	.word	0x6d632f2f
  a4:	7478652d 	.word	0x7478652d
  a8:	7665642e 	.word	0x7665642e
  ac:	696e6f2e 	.word	0x696e6f2e
  b0:	2e6f6574 	.word	0x2e6f6574
  b4:	2f6d6f63 	.word	0x2f6d6f63
  b8:	2f6e7673 	.word	0x2f6e7673
  bc:	6f6e616e 	.word	0x6f6e616e
  c0:	2f766564 	.word	0x2f766564
  c4:	6b636170 	.word	0x6b636170
  c8:	73656761 	.word	0x73656761
  cc:	6365732f 	.word	0x6365732f
  d0:	5f657275 	.word	0x5f657275
  d4:	736f6962 	.word	0x736f6962
  d8:	6172622f 	.word	0x6172622f
  dc:	6568636e 	.word	0x6568636e
  e0:	61682f73 	.word	0x61682f73
  e4:	636f7073 	.word	0x636f7073
  e8:	6b69682f 	.word	0x6b69682f
  ec:	732f7965 	.word	0x732f7965
  f0:	72756365 	.word	0x72756365
  f4:	69625f65 	.word	0x69625f65
  f8:	702f736f 	.word	0x702f736f
  fc:	622f696b 	.word	0x622f696b
 100:	756e6769 	.word	0x756e6769
 104:	20632e6d 	.word	0x20632e6d
 108:	52242024 	.word	0x52242024
 10c:	73697665 	.word	0x73697665
 110:	3a6e6f69 	.word	0x3a6e6f69
 114:	30363220 	.word	0x30363220
 118:	24203530 	.word	0x24203530
 11c:	00000000 	.word	0x00000000

Disassembly of section .text.internal_mul:

0000000000000000 <internal_mul>:
   0:	d10103ff 	sub	sp, sp, #0x40
   4:	f9000fe0 	str	x0, [sp,#24]
   8:	f9000be1 	str	x1, [sp,#16]
   c:	f90007e2 	str	x2, [sp,#8]
  10:	b90007e3 	str	w3, [sp,#4]
  14:	b9003bff 	str	wzr, [sp,#56]
  18:	14000009 	b	3c <internal_mul+0x3c>
  1c:	b9803be0 	ldrsw	x0, [sp,#56]
  20:	d37ff800 	lsl	x0, x0, #1
  24:	f94007e1 	ldr	x1, [sp,#8]
  28:	8b000020 	add	x0, x1, x0
  2c:	7900001f 	strh	wzr, [x0]
  30:	b9403be0 	ldr	w0, [sp,#56]
  34:	11000400 	add	w0, w0, #0x1
  38:	b9003be0 	str	w0, [sp,#56]
  3c:	b94007e0 	ldr	w0, [sp,#4]
  40:	531f7801 	lsl	w1, w0, #1
  44:	b9403be0 	ldr	w0, [sp,#56]
  48:	6b00003f 	cmp	w1, w0
  4c:	54fffe8c 	b.gt	1c <internal_mul+0x1c>
  50:	b94007e0 	ldr	w0, [sp,#4]
  54:	51000400 	sub	w0, w0, #0x1
  58:	b9003fe0 	str	w0, [sp,#60]
  5c:	14000043 	b	168 <internal_mul+0x168>
  60:	b9803fe0 	ldrsw	x0, [sp,#60]
  64:	d37ff800 	lsl	x0, x0, #1
  68:	f9400fe1 	ldr	x1, [sp,#24]
  6c:	8b000020 	add	x0, x1, x0
  70:	79400000 	ldrh	w0, [x0]
  74:	53003c00 	uxth	w0, w0
  78:	f90017e0 	str	x0, [sp,#40]
  7c:	f9001bff 	str	xzr, [sp,#48]
  80:	b94007e0 	ldr	w0, [sp,#4]
  84:	51000400 	sub	w0, w0, #0x1
  88:	b9003be0 	str	w0, [sp,#56]
  8c:	1400002a 	b	134 <internal_mul+0x134>
  90:	b9803be0 	ldrsw	x0, [sp,#56]
  94:	d37ff800 	lsl	x0, x0, #1
  98:	f9400be1 	ldr	x1, [sp,#16]
  9c:	8b000020 	add	x0, x1, x0
  a0:	79400000 	ldrh	w0, [x0]
  a4:	53003c01 	uxth	w1, w0
  a8:	f94017e0 	ldr	x0, [sp,#40]
  ac:	9b007c20 	mul	x0, x1, x0
  b0:	f9401be1 	ldr	x1, [sp,#48]
  b4:	8b000020 	add	x0, x1, x0
  b8:	f9001be0 	str	x0, [sp,#48]
  bc:	b9403fe1 	ldr	w1, [sp,#60]
  c0:	b9403be0 	ldr	w0, [sp,#56]
  c4:	0b000020 	add	w0, w1, w0
  c8:	93407c00 	sxtw	x0, w0
  cc:	91000400 	add	x0, x0, #0x1
  d0:	d37ff800 	lsl	x0, x0, #1
  d4:	f94007e1 	ldr	x1, [sp,#8]
  d8:	8b000020 	add	x0, x1, x0
  dc:	79400000 	ldrh	w0, [x0]
  e0:	53003c00 	uxth	w0, w0
  e4:	f9401be1 	ldr	x1, [sp,#48]
  e8:	8b000020 	add	x0, x1, x0
  ec:	f9001be0 	str	x0, [sp,#48]
  f0:	b9403fe1 	ldr	w1, [sp,#60]
  f4:	b9403be0 	ldr	w0, [sp,#56]
  f8:	0b000020 	add	w0, w1, w0
  fc:	93407c00 	sxtw	x0, w0
 100:	91000400 	add	x0, x0, #0x1
 104:	d37ff800 	lsl	x0, x0, #1
 108:	f94007e1 	ldr	x1, [sp,#8]
 10c:	8b000020 	add	x0, x1, x0
 110:	f9401be1 	ldr	x1, [sp,#48]
 114:	53003c21 	uxth	w1, w1
 118:	79000001 	strh	w1, [x0]
 11c:	f9401be0 	ldr	x0, [sp,#48]
 120:	d350fc00 	lsr	x0, x0, #16
 124:	f9001be0 	str	x0, [sp,#48]
 128:	b9403be0 	ldr	w0, [sp,#56]
 12c:	51000400 	sub	w0, w0, #0x1
 130:	b9003be0 	str	w0, [sp,#56]
 134:	b9403be0 	ldr	w0, [sp,#56]
 138:	6b1f001f 	cmp	w0, wzr
 13c:	54fffaaa 	b.ge	90 <internal_mul+0x90>
 140:	b9803fe0 	ldrsw	x0, [sp,#60]
 144:	d37ff800 	lsl	x0, x0, #1
 148:	f94007e1 	ldr	x1, [sp,#8]
 14c:	8b000020 	add	x0, x1, x0
 150:	f9401be1 	ldr	x1, [sp,#48]
 154:	53003c21 	uxth	w1, w1
 158:	79000001 	strh	w1, [x0]
 15c:	b9403fe0 	ldr	w0, [sp,#60]
 160:	51000400 	sub	w0, w0, #0x1
 164:	b9003fe0 	str	w0, [sp,#60]
 168:	b9403fe0 	ldr	w0, [sp,#60]
 16c:	6b1f001f 	cmp	w0, wzr
 170:	54fff78a 	b.ge	60 <internal_mul+0x60>
 174:	910103ff 	add	sp, sp, #0x40
 178:	d65f03c0 	ret

Disassembly of section .text.internal_add_shifted:

0000000000000000 <internal_add_shifted>:
   0:	d100c3ff 	sub	sp, sp, #0x30
   4:	f90007e0 	str	x0, [sp,#8]
   8:	b90007e1 	str	w1, [sp,#4]
   c:	b90003e2 	str	w2, [sp]
  10:	b94003e0 	ldr	w0, [sp]
  14:	11003c01 	add	w1, w0, #0xf
  18:	6b1f001f 	cmp	w0, wzr
  1c:	1a80b020 	csel	w0, w1, w0, lt
  20:	13047c00 	asr	w0, w0, #4
  24:	11000400 	add	w0, w0, #0x1
  28:	b9002fe0 	str	w0, [sp,#44]
  2c:	b94003e1 	ldr	w1, [sp]
  30:	131f7c20 	asr	w0, w1, #31
  34:	531c7c00 	lsr	w0, w0, #28
  38:	0b000021 	add	w1, w1, w0
  3c:	12000c21 	and	w1, w1, #0xf
  40:	4b000020 	sub	w0, w1, w0
  44:	b9001fe0 	str	w0, [sp,#28]
  48:	b9401fe0 	ldr	w0, [sp,#28]
  4c:	b94007e1 	ldr	w1, [sp,#4]
  50:	1ac02020 	lsl	w0, w1, w0
  54:	2a0003e0 	mov	w0, w0
  58:	f90013e0 	str	x0, [sp,#32]
  5c:	14000017 	b	b8 <internal_add_shifted+0xb8>
  60:	b9802fe0 	ldrsw	x0, [sp,#44]
  64:	d37ff800 	lsl	x0, x0, #1
  68:	f94007e1 	ldr	x1, [sp,#8]
  6c:	8b000020 	add	x0, x1, x0
  70:	79400000 	ldrh	w0, [x0]
  74:	53003c00 	uxth	w0, w0
  78:	f94013e1 	ldr	x1, [sp,#32]
  7c:	8b000020 	add	x0, x1, x0
  80:	f90013e0 	str	x0, [sp,#32]
  84:	b9802fe0 	ldrsw	x0, [sp,#44]
  88:	d37ff800 	lsl	x0, x0, #1
  8c:	f94007e1 	ldr	x1, [sp,#8]
  90:	8b000020 	add	x0, x1, x0
  94:	f94013e1 	ldr	x1, [sp,#32]
  98:	53003c21 	uxth	w1, w1
  9c:	79000001 	strh	w1, [x0]
  a0:	f94013e0 	ldr	x0, [sp,#32]
  a4:	d350fc00 	lsr	x0, x0, #16
  a8:	f90013e0 	str	x0, [sp,#32]
  ac:	b9402fe0 	ldr	w0, [sp,#44]
  b0:	11000400 	add	w0, w0, #0x1
  b4:	b9002fe0 	str	w0, [sp,#44]
  b8:	f94013e0 	ldr	x0, [sp,#32]
  bc:	eb1f001f 	cmp	x0, xzr
  c0:	54fffd01 	b.ne	60 <internal_add_shifted+0x60>
  c4:	9100c3ff 	add	sp, sp, #0x30
  c8:	d65f03c0 	ret

Disassembly of section .text.internal_mod:

0000000000000000 <internal_mod>:
   0:	a9b97bfd 	stp	x29, x30, [sp,#-112]!
   4:	910003fd 	mov	x29, sp
   8:	f9001fa0 	str	x0, [x29,#56]
   c:	b90037a1 	str	w1, [x29,#52]
  10:	f90017a2 	str	x2, [x29,#40]
  14:	b90033a3 	str	w3, [x29,#48]
  18:	f90013a4 	str	x4, [x29,#32]
  1c:	b9001fa5 	str	w5, [x29,#28]
  20:	f94017a0 	ldr	x0, [x29,#40]
  24:	79400000 	ldrh	w0, [x0]
  28:	790097a0 	strh	w0, [x29,#74]
  2c:	b94033a0 	ldr	w0, [x29,#48]
  30:	7100041f 	cmp	w0, #0x1
  34:	540000ad 	b.le	48 <internal_mod+0x48>
  38:	f94017a0 	ldr	x0, [x29,#40]
  3c:	79400400 	ldrh	w0, [x0,#2]
  40:	7900dfa0 	strh	w0, [x29,#110]
  44:	14000002 	b	4c <internal_mod+0x4c>
  48:	7900dfbf 	strh	wzr, [x29,#110]
  4c:	b90067bf 	str	wzr, [x29,#100]
  50:	140000de 	b	3c8 <internal_mod+0x3c8>
  54:	b94067a0 	ldr	w0, [x29,#100]
  58:	6b1f001f 	cmp	w0, wzr
  5c:	54000061 	b.ne	68 <internal_mod+0x68>
  60:	b9006bbf 	str	wzr, [x29,#104]
  64:	1400000e 	b	9c <internal_mod+0x9c>
  68:	b98067a0 	ldrsw	x0, [x29,#100]
  6c:	d37ff800 	lsl	x0, x0, #1
  70:	d1000800 	sub	x0, x0, #0x2
  74:	f9401fa1 	ldr	x1, [x29,#56]
  78:	8b000020 	add	x0, x1, x0
  7c:	79400000 	ldrh	w0, [x0]
  80:	b9006ba0 	str	w0, [x29,#104]
  84:	b98067a0 	ldrsw	x0, [x29,#100]
  88:	d37ff800 	lsl	x0, x0, #1
  8c:	d1000800 	sub	x0, x0, #0x2
  90:	f9401fa1 	ldr	x1, [x29,#56]
  94:	8b000020 	add	x0, x1, x0
  98:	7900001f 	strh	wzr, [x0]
  9c:	b94037a0 	ldr	w0, [x29,#52]
  a0:	51000401 	sub	w1, w0, #0x1
  a4:	b94067a0 	ldr	w0, [x29,#100]
  a8:	6b00003f 	cmp	w1, w0
  ac:	54000061 	b.ne	b8 <internal_mod+0xb8>
  b0:	b9004fbf 	str	wzr, [x29,#76]
  b4:	14000008 	b	d4 <internal_mod+0xd4>
  b8:	b98067a0 	ldrsw	x0, [x29,#100]
  bc:	91000400 	add	x0, x0, #0x1
  c0:	d37ff800 	lsl	x0, x0, #1
  c4:	f9401fa1 	ldr	x1, [x29,#56]
  c8:	8b000020 	add	x0, x1, x0
  cc:	79400000 	ldrh	w0, [x0]
  d0:	b9004fa0 	str	w0, [x29,#76]
  d4:	b9406ba0 	ldr	w0, [x29,#104]
  d8:	d370bc01 	lsl	x1, x0, #16
  dc:	b98067a0 	ldrsw	x0, [x29,#100]
  e0:	d37ff800 	lsl	x0, x0, #1
  e4:	f9401fa2 	ldr	x2, [x29,#56]
  e8:	8b000040 	add	x0, x2, x0
  ec:	79400000 	ldrh	w0, [x0]
  f0:	53003c00 	uxth	w0, w0
  f4:	8b000020 	add	x0, x1, x0
  f8:	f9002fa0 	str	x0, [x29,#88]
  fc:	794097a0 	ldrh	w0, [x29,#74]
 100:	f9402fa1 	ldr	x1, [x29,#88]
 104:	9ac00820 	udiv	x0, x1, x0
 108:	b90057a0 	str	w0, [x29,#84]
 10c:	794097a1 	ldrh	w1, [x29,#74]
 110:	f9402fa0 	ldr	x0, [x29,#88]
 114:	9ac10802 	udiv	x2, x0, x1
 118:	9b017c41 	mul	x1, x2, x1
 11c:	cb010000 	sub	x0, x0, x1
 120:	b90047a0 	str	w0, [x29,#68]
 124:	7940dfa1 	ldrh	w1, [x29,#110]
 128:	b94057a0 	ldr	w0, [x29,#84]
 12c:	9b007c20 	mul	x0, x1, x0
 130:	f9002fa0 	str	x0, [x29,#88]
 134:	b94047a0 	ldr	w0, [x29,#68]
 138:	d370bc01 	lsl	x1, x0, #16
 13c:	b9404fa0 	ldr	w0, [x29,#76]
 140:	8b000021 	add	x1, x1, x0
 144:	f9402fa0 	ldr	x0, [x29,#88]
 148:	eb00003f 	cmp	x1, x0
 14c:	54000362 	b.cs	1b8 <internal_mod+0x1b8>
 150:	b94057a0 	ldr	w0, [x29,#84]
 154:	51000400 	sub	w0, w0, #0x1
 158:	b90057a0 	str	w0, [x29,#84]
 15c:	7940dfa0 	ldrh	w0, [x29,#110]
 160:	f9402fa1 	ldr	x1, [x29,#88]
 164:	cb000020 	sub	x0, x1, x0
 168:	f9002fa0 	str	x0, [x29,#88]
 16c:	794097a1 	ldrh	w1, [x29,#74]
 170:	b94047a0 	ldr	w0, [x29,#68]
 174:	0b000020 	add	w0, w1, w0
 178:	12003c00 	and	w0, w0, #0xffff
 17c:	b90047a0 	str	w0, [x29,#68]
 180:	794097a1 	ldrh	w1, [x29,#74]
 184:	b94047a0 	ldr	w0, [x29,#68]
 188:	6b00003f 	cmp	w1, w0
 18c:	54000168 	b.hi	1b8 <internal_mod+0x1b8>
 190:	b94047a0 	ldr	w0, [x29,#68]
 194:	d370bc01 	lsl	x1, x0, #16
 198:	b9404fa0 	ldr	w0, [x29,#76]
 19c:	8b000021 	add	x1, x1, x0
 1a0:	f9402fa0 	ldr	x0, [x29,#88]
 1a4:	eb00003f 	cmp	x1, x0
 1a8:	54000082 	b.cs	1b8 <internal_mod+0x1b8>
 1ac:	b94057a0 	ldr	w0, [x29,#84]
 1b0:	51000400 	sub	w0, w0, #0x1
 1b4:	b90057a0 	str	w0, [x29,#84]
 1b8:	b90053bf 	str	wzr, [x29,#80]
 1bc:	b94033a0 	ldr	w0, [x29,#48]
 1c0:	51000400 	sub	w0, w0, #0x1
 1c4:	b90063a0 	str	w0, [x29,#96]
 1c8:	14000037 	b	2a4 <internal_mod+0x2a4>
 1cc:	b94057a1 	ldr	w1, [x29,#84]
 1d0:	b98063a0 	ldrsw	x0, [x29,#96]
 1d4:	d37ff800 	lsl	x0, x0, #1
 1d8:	f94017a2 	ldr	x2, [x29,#40]
 1dc:	8b000040 	add	x0, x2, x0
 1e0:	79400000 	ldrh	w0, [x0]
 1e4:	53003c00 	uxth	w0, w0
 1e8:	9b007c20 	mul	x0, x1, x0
 1ec:	f9002fa0 	str	x0, [x29,#88]
 1f0:	b94053a0 	ldr	w0, [x29,#80]
 1f4:	f9402fa1 	ldr	x1, [x29,#88]
 1f8:	8b000020 	add	x0, x1, x0
 1fc:	f9002fa0 	str	x0, [x29,#88]
 200:	f9402fa0 	ldr	x0, [x29,#88]
 204:	d350fc00 	lsr	x0, x0, #16
 208:	b90053a0 	str	w0, [x29,#80]
 20c:	f9402fa0 	ldr	x0, [x29,#88]
 210:	53003c01 	uxth	w1, w0
 214:	b94067a2 	ldr	w2, [x29,#100]
 218:	b94063a0 	ldr	w0, [x29,#96]
 21c:	0b000040 	add	w0, w2, w0
 220:	93407c00 	sxtw	x0, w0
 224:	d37ff800 	lsl	x0, x0, #1
 228:	f9401fa2 	ldr	x2, [x29,#56]
 22c:	8b000040 	add	x0, x2, x0
 230:	79400000 	ldrh	w0, [x0]
 234:	6b00003f 	cmp	w1, w0
 238:	54000089 	b.ls	248 <internal_mod+0x248>
 23c:	b94053a0 	ldr	w0, [x29,#80]
 240:	11000400 	add	w0, w0, #0x1
 244:	b90053a0 	str	w0, [x29,#80]
 248:	b94067a1 	ldr	w1, [x29,#100]
 24c:	b94063a0 	ldr	w0, [x29,#96]
 250:	0b000020 	add	w0, w1, w0
 254:	93407c00 	sxtw	x0, w0
 258:	d37ff800 	lsl	x0, x0, #1
 25c:	f9401fa1 	ldr	x1, [x29,#56]
 260:	8b000020 	add	x0, x1, x0
 264:	b94067a2 	ldr	w2, [x29,#100]
 268:	b94063a1 	ldr	w1, [x29,#96]
 26c:	0b010041 	add	w1, w2, w1
 270:	93407c21 	sxtw	x1, w1
 274:	d37ff821 	lsl	x1, x1, #1
 278:	f9401fa2 	ldr	x2, [x29,#56]
 27c:	8b010041 	add	x1, x2, x1
 280:	79400022 	ldrh	w2, [x1]
 284:	f9402fa1 	ldr	x1, [x29,#88]
 288:	53003c21 	uxth	w1, w1
 28c:	4b010041 	sub	w1, w2, w1
 290:	53003c21 	uxth	w1, w1
 294:	79000001 	strh	w1, [x0]
 298:	b94063a0 	ldr	w0, [x29,#96]
 29c:	51000400 	sub	w0, w0, #0x1
 2a0:	b90063a0 	str	w0, [x29,#96]
 2a4:	b94063a0 	ldr	w0, [x29,#96]
 2a8:	6b1f001f 	cmp	w0, wzr
 2ac:	54fff90a 	b.ge	1cc <internal_mod+0x1cc>
 2b0:	b94053a1 	ldr	w1, [x29,#80]
 2b4:	b9406ba0 	ldr	w0, [x29,#104]
 2b8:	6b00003f 	cmp	w1, w0
 2bc:	54000620 	b.eq	380 <internal_mod+0x380>
 2c0:	f9002fbf 	str	xzr, [x29,#88]
 2c4:	b94033a0 	ldr	w0, [x29,#48]
 2c8:	51000400 	sub	w0, w0, #0x1
 2cc:	b90063a0 	str	w0, [x29,#96]
 2d0:	14000026 	b	368 <internal_mod+0x368>
 2d4:	b98063a0 	ldrsw	x0, [x29,#96]
 2d8:	d37ff800 	lsl	x0, x0, #1
 2dc:	f94017a1 	ldr	x1, [x29,#40]
 2e0:	8b000020 	add	x0, x1, x0
 2e4:	79400000 	ldrh	w0, [x0]
 2e8:	53003c00 	uxth	w0, w0
 2ec:	f9402fa1 	ldr	x1, [x29,#88]
 2f0:	8b000020 	add	x0, x1, x0
 2f4:	f9002fa0 	str	x0, [x29,#88]
 2f8:	b94067a1 	ldr	w1, [x29,#100]
 2fc:	b94063a0 	ldr	w0, [x29,#96]
 300:	0b000020 	add	w0, w1, w0
 304:	93407c00 	sxtw	x0, w0
 308:	d37ff800 	lsl	x0, x0, #1
 30c:	f9401fa1 	ldr	x1, [x29,#56]
 310:	8b000020 	add	x0, x1, x0
 314:	79400000 	ldrh	w0, [x0]
 318:	53003c00 	uxth	w0, w0
 31c:	f9402fa1 	ldr	x1, [x29,#88]
 320:	8b000020 	add	x0, x1, x0
 324:	f9002fa0 	str	x0, [x29,#88]
 328:	b94067a1 	ldr	w1, [x29,#100]
 32c:	b94063a0 	ldr	w0, [x29,#96]
 330:	0b000020 	add	w0, w1, w0
 334:	93407c00 	sxtw	x0, w0
 338:	d37ff800 	lsl	x0, x0, #1
 33c:	f9401fa1 	ldr	x1, [x29,#56]
 340:	8b000020 	add	x0, x1, x0
 344:	f9402fa1 	ldr	x1, [x29,#88]
 348:	53003c21 	uxth	w1, w1
 34c:	79000001 	strh	w1, [x0]
 350:	f9402fa0 	ldr	x0, [x29,#88]
 354:	d350fc00 	lsr	x0, x0, #16
 358:	f9002fa0 	str	x0, [x29,#88]
 35c:	b94063a0 	ldr	w0, [x29,#96]
 360:	51000400 	sub	w0, w0, #0x1
 364:	b90063a0 	str	w0, [x29,#96]
 368:	b94063a0 	ldr	w0, [x29,#96]
 36c:	6b1f001f 	cmp	w0, wzr
 370:	54fffb2a 	b.ge	2d4 <internal_mod+0x2d4>
 374:	b94057a0 	ldr	w0, [x29,#84]
 378:	51000400 	sub	w0, w0, #0x1
 37c:	b90057a0 	str	w0, [x29,#84]
 380:	f94013a0 	ldr	x0, [x29,#32]
 384:	eb1f001f 	cmp	x0, xzr
 388:	540001a0 	b.eq	3bc <internal_mod+0x3bc>
 38c:	b94037a1 	ldr	w1, [x29,#52]
 390:	b94033a0 	ldr	w0, [x29,#48]
 394:	4b000021 	sub	w1, w1, w0
 398:	b94067a0 	ldr	w0, [x29,#100]
 39c:	4b000020 	sub	w0, w1, w0
 3a0:	531c6c01 	lsl	w1, w0, #4
 3a4:	b9401fa0 	ldr	w0, [x29,#28]
 3a8:	0b000020 	add	w0, w1, w0
 3ac:	2a0003e2 	mov	w2, w0
 3b0:	b94057a1 	ldr	w1, [x29,#84]
 3b4:	f94013a0 	ldr	x0, [x29,#32]
 3b8:	94000000 	bl	0 <internal_mod>
 3bc:	b94067a0 	ldr	w0, [x29,#100]
 3c0:	11000400 	add	w0, w0, #0x1
 3c4:	b90067a0 	str	w0, [x29,#100]
 3c8:	b94037a1 	ldr	w1, [x29,#52]
 3cc:	b94033a0 	ldr	w0, [x29,#48]
 3d0:	4b000021 	sub	w1, w1, w0
 3d4:	b94067a0 	ldr	w0, [x29,#100]
 3d8:	6b00003f 	cmp	w1, w0
 3dc:	54ffe3ca 	b.ge	54 <internal_mod+0x54>
 3e0:	a8c77bfd 	ldp	x29, x30, [sp],#112
 3e4:	d65f03c0 	ret

Disassembly of section .text.newbn:

0000000000000000 <newbn>:
   0:	a9bd7bfd 	stp	x29, x30, [sp,#-48]!
   4:	910003fd 	mov	x29, sp
   8:	b9001fa0 	str	w0, [x29,#28]
   c:	b9401fa0 	ldr	w0, [x29,#28]
  10:	11000400 	add	w0, w0, #0x1
  14:	93407c00 	sxtw	x0, w0
  18:	d37ff800 	lsl	x0, x0, #1
  1c:	d2800201 	mov	x1, #0x10                  	// #16
  20:	94000000 	bl	0 <NMemAlloc_align>
  24:	f90017a0 	str	x0, [x29,#40]
  28:	f94017a0 	ldr	x0, [x29,#40]
  2c:	eb1f001f 	cmp	x0, xzr
  30:	54000061 	b.ne	3c <newbn+0x3c>
  34:	d2800000 	mov	x0, #0x0                   	// #0
  38:	1400000e 	b	70 <newbn+0x70>
  3c:	b9401fa0 	ldr	w0, [x29,#28]
  40:	11000400 	add	w0, w0, #0x1
  44:	93407c00 	sxtw	x0, w0
  48:	d37ff800 	lsl	x0, x0, #1
  4c:	aa0003e2 	mov	x2, x0
  50:	52800001 	mov	w1, #0x0                   	// #0
  54:	f94017a0 	ldr	x0, [x29,#40]
  58:	94000000 	bl	0 <NMemSet>
  5c:	b9401fa0 	ldr	w0, [x29,#28]
  60:	53003c01 	uxth	w1, w0
  64:	f94017a0 	ldr	x0, [x29,#40]
  68:	79000001 	strh	w1, [x0]
  6c:	f94017a0 	ldr	x0, [x29,#40]
  70:	a8c37bfd 	ldp	x29, x30, [sp],#48
  74:	d65f03c0 	ret

Disassembly of section .text.freebn:

0000000000000000 <freebn>:
   0:	a9be7bfd 	stp	x29, x30, [sp,#-32]!
   4:	910003fd 	mov	x29, sp
   8:	f9000fa0 	str	x0, [x29,#24]
   c:	f9400fa0 	ldr	x0, [x29,#24]
  10:	79400000 	ldrh	w0, [x0]
  14:	11000400 	add	w0, w0, #0x1
  18:	93407c00 	sxtw	x0, w0
  1c:	d37ff800 	lsl	x0, x0, #1
  20:	aa0003e2 	mov	x2, x0
  24:	52800001 	mov	w1, #0x0                   	// #0
  28:	f9400fa0 	ldr	x0, [x29,#24]
  2c:	94000000 	bl	0 <NMemSet>
  30:	f9400fa0 	ldr	x0, [x29,#24]
  34:	94000000 	bl	0 <NMemFree>
  38:	a8c27bfd 	ldp	x29, x30, [sp],#32
  3c:	d65f03c0 	ret

Disassembly of section .text.bignum_from_bytes:

0000000000000000 <bignum_from_bytes>:
   0:	a9bc7bfd 	stp	x29, x30, [sp,#-64]!
   4:	910003fd 	mov	x29, sp
   8:	f9000fa0 	str	x0, [x29,#24]
   c:	b90017a1 	str	w1, [x29,#20]
  10:	b94017a0 	ldr	w0, [x29,#20]
  14:	11000400 	add	w0, w0, #0x1
  18:	531f7c01 	lsr	w1, w0, #31
  1c:	0b000020 	add	w0, w1, w0
  20:	13017c00 	asr	w0, w0, #1
  24:	b9003ba0 	str	w0, [x29,#56]
  28:	b9403ba0 	ldr	w0, [x29,#56]
  2c:	94000000 	bl	0 <bignum_from_bytes>
  30:	f9001ba0 	str	x0, [x29,#48]
  34:	52800020 	mov	w0, #0x1                   	// #1
  38:	b9003fa0 	str	w0, [x29,#60]
  3c:	14000009 	b	60 <bignum_from_bytes+0x60>
  40:	b9803fa0 	ldrsw	x0, [x29,#60]
  44:	d37ff800 	lsl	x0, x0, #1
  48:	f9401ba1 	ldr	x1, [x29,#48]
  4c:	8b000020 	add	x0, x1, x0
  50:	7900001f 	strh	wzr, [x0]
  54:	b9403fa0 	ldr	w0, [x29,#60]
  58:	11000400 	add	w0, w0, #0x1
  5c:	b9003fa0 	str	w0, [x29,#60]
  60:	b9403fa1 	ldr	w1, [x29,#60]
  64:	b9403ba0 	ldr	w0, [x29,#56]
  68:	6b00003f 	cmp	w1, w0
  6c:	54fffead 	b.le	40 <bignum_from_bytes+0x40>
  70:	b94017a0 	ldr	w0, [x29,#20]
  74:	b9003fa0 	str	w0, [x29,#60]
  78:	14000036 	b	150 <bignum_from_bytes+0x150>
  7c:	f9400fa0 	ldr	x0, [x29,#24]
  80:	91000401 	add	x1, x0, #0x1
  84:	f9000fa1 	str	x1, [x29,#24]
  88:	39400000 	ldrb	w0, [x0]
  8c:	3900bfa0 	strb	w0, [x29,#47]
  90:	b9403fa0 	ldr	w0, [x29,#60]
  94:	12000000 	and	w0, w0, #0x1
  98:	6b1f001f 	cmp	w0, wzr
  9c:	54000320 	b.eq	100 <bignum_from_bytes+0x100>
  a0:	b9403fa0 	ldr	w0, [x29,#60]
  a4:	531f7c01 	lsr	w1, w0, #31
  a8:	0b000020 	add	w0, w1, w0
  ac:	13017c00 	asr	w0, w0, #1
  b0:	11000401 	add	w1, w0, #0x1
  b4:	93407c21 	sxtw	x1, w1
  b8:	d37ff821 	lsl	x1, x1, #1
  bc:	f9401ba2 	ldr	x2, [x29,#48]
  c0:	8b010041 	add	x1, x2, x1
  c4:	11000400 	add	w0, w0, #0x1
  c8:	93407c00 	sxtw	x0, w0
  cc:	d37ff800 	lsl	x0, x0, #1
  d0:	f9401ba2 	ldr	x2, [x29,#48]
  d4:	8b000040 	add	x0, x2, x0
  d8:	79400000 	ldrh	w0, [x0]
  dc:	13003c02 	sxth	w2, w0
  e0:	3940bfa0 	ldrb	w0, [x29,#47]
  e4:	53185c00 	lsl	w0, w0, #8
  e8:	13003c00 	sxth	w0, w0
  ec:	2a000040 	orr	w0, w2, w0
  f0:	13003c00 	sxth	w0, w0
  f4:	53003c00 	uxth	w0, w0
  f8:	79000020 	strh	w0, [x1]
  fc:	14000015 	b	150 <bignum_from_bytes+0x150>
 100:	b9403fa0 	ldr	w0, [x29,#60]
 104:	531f7c01 	lsr	w1, w0, #31
 108:	0b000020 	add	w0, w1, w0
 10c:	13017c00 	asr	w0, w0, #1
 110:	11000401 	add	w1, w0, #0x1
 114:	93407c21 	sxtw	x1, w1
 118:	d37ff821 	lsl	x1, x1, #1
 11c:	f9401ba2 	ldr	x2, [x29,#48]
 120:	8b010041 	add	x1, x2, x1
 124:	11000400 	add	w0, w0, #0x1
 128:	93407c00 	sxtw	x0, w0
 12c:	d37ff800 	lsl	x0, x0, #1
 130:	f9401ba2 	ldr	x2, [x29,#48]
 134:	8b000040 	add	x0, x2, x0
 138:	79400002 	ldrh	w2, [x0]
 13c:	3940bfa0 	ldrb	w0, [x29,#47]
 140:	53003c00 	uxth	w0, w0
 144:	2a000040 	orr	w0, w2, w0
 148:	53003c00 	uxth	w0, w0
 14c:	79000020 	strh	w0, [x1]
 150:	b9403fa0 	ldr	w0, [x29,#60]
 154:	51000401 	sub	w1, w0, #0x1
 158:	b9003fa1 	str	w1, [x29,#60]
 15c:	6b1f001f 	cmp	w0, wzr
 160:	54fff8e1 	b.ne	7c <bignum_from_bytes+0x7c>
 164:	14000007 	b	180 <bignum_from_bytes+0x180>
 168:	f9401ba0 	ldr	x0, [x29,#48]
 16c:	79400000 	ldrh	w0, [x0]
 170:	51000400 	sub	w0, w0, #0x1
 174:	53003c01 	uxth	w1, w0
 178:	f9401ba0 	ldr	x0, [x29,#48]
 17c:	79000001 	strh	w1, [x0]
 180:	f9401ba0 	ldr	x0, [x29,#48]
 184:	79400000 	ldrh	w0, [x0]
 188:	7100041f 	cmp	w0, #0x1
 18c:	54000149 	b.ls	1b4 <bignum_from_bytes+0x1b4>
 190:	f9401ba0 	ldr	x0, [x29,#48]
 194:	79400000 	ldrh	w0, [x0]
 198:	53003c00 	uxth	w0, w0
 19c:	d37ff800 	lsl	x0, x0, #1
 1a0:	f9401ba1 	ldr	x1, [x29,#48]
 1a4:	8b000020 	add	x0, x1, x0
 1a8:	79400000 	ldrh	w0, [x0]
 1ac:	6b1f001f 	cmp	w0, wzr
 1b0:	54fffdc0 	b.eq	168 <bignum_from_bytes+0x168>
 1b4:	f9401ba0 	ldr	x0, [x29,#48]
 1b8:	a8c47bfd 	ldp	x29, x30, [sp],#64
 1bc:	d65f03c0 	ret

Disassembly of section .text.bytes_from_bignum:

0000000000000000 <bytes_from_bignum>:
   0:	a9bd7bfd 	stp	x29, x30, [sp,#-48]!
   4:	910003fd 	mov	x29, sp
   8:	f9000fa0 	str	x0, [x29,#24]
   c:	f9000ba1 	str	x1, [x29,#16]
  10:	f9400fa0 	ldr	x0, [x29,#24]
  14:	79400000 	ldrh	w0, [x0]
  18:	790057a0 	strh	w0, [x29,#42]
  1c:	794057a0 	ldrh	w0, [x29,#42]
  20:	d37ff800 	lsl	x0, x0, #1
  24:	f9400fa1 	ldr	x1, [x29,#24]
  28:	8b000020 	add	x0, x1, x0
  2c:	79400000 	ldrh	w0, [x0]
  30:	7103fc1f 	cmp	w0, #0xff
  34:	54000128 	b.hi	58 <bytes_from_bignum+0x58>
  38:	794057a0 	ldrh	w0, [x29,#42]
  3c:	531f7800 	lsl	w0, w0, #1
  40:	53003c00 	uxth	w0, w0
  44:	51000400 	sub	w0, w0, #0x1
  48:	53003c01 	uxth	w1, w0
  4c:	f9400ba0 	ldr	x0, [x29,#16]
  50:	79000001 	strh	w1, [x0]
  54:	14000006 	b	6c <bytes_from_bignum+0x6c>
  58:	794057a0 	ldrh	w0, [x29,#42]
  5c:	531f7800 	lsl	w0, w0, #1
  60:	53003c01 	uxth	w1, w0
  64:	f9400ba0 	ldr	x0, [x29,#16]
  68:	79000001 	strh	w1, [x0]
  6c:	f9400ba0 	ldr	x0, [x29,#16]
  70:	79400000 	ldrh	w0, [x0]
  74:	53003c00 	uxth	w0, w0
  78:	d2800201 	mov	x1, #0x10                  	// #16
  7c:	94000000 	bl	0 <NMemAlloc_align>
  80:	f90013a0 	str	x0, [x29,#32]
  84:	52800020 	mov	w0, #0x1                   	// #1
  88:	79005fa0 	strh	w0, [x29,#46]
  8c:	794057a0 	ldrh	w0, [x29,#42]
  90:	79005ba0 	strh	w0, [x29,#44]
  94:	14000037 	b	170 <bytes_from_bignum+0x170>
  98:	79405fa0 	ldrh	w0, [x29,#46]
  9c:	7100041f 	cmp	w0, #0x1
  a0:	540002e1 	b.ne	fc <bytes_from_bignum+0xfc>
  a4:	794057a0 	ldrh	w0, [x29,#42]
  a8:	d37ff800 	lsl	x0, x0, #1
  ac:	f9400fa1 	ldr	x1, [x29,#24]
  b0:	8b000020 	add	x0, x1, x0
  b4:	79400000 	ldrh	w0, [x0]
  b8:	7103fc1f 	cmp	w0, #0xff
  bc:	54000208 	b.hi	fc <bytes_from_bignum+0xfc>
  c0:	79405fa0 	ldrh	w0, [x29,#46]
  c4:	d1000400 	sub	x0, x0, #0x1
  c8:	f94013a1 	ldr	x1, [x29,#32]
  cc:	8b000020 	add	x0, x1, x0
  d0:	79405ba1 	ldrh	w1, [x29,#44]
  d4:	d37ff821 	lsl	x1, x1, #1
  d8:	f9400fa2 	ldr	x2, [x29,#24]
  dc:	8b010041 	add	x1, x2, x1
  e0:	79400021 	ldrh	w1, [x1]
  e4:	53001c21 	uxtb	w1, w1
  e8:	39000001 	strb	w1, [x0]
  ec:	79405fa0 	ldrh	w0, [x29,#46]
  f0:	51000400 	sub	w0, w0, #0x1
  f4:	79005fa0 	strh	w0, [x29,#46]
  f8:	14000018 	b	158 <bytes_from_bignum+0x158>
  fc:	79405fa0 	ldrh	w0, [x29,#46]
 100:	d1000400 	sub	x0, x0, #0x1
 104:	f94013a1 	ldr	x1, [x29,#32]
 108:	8b000020 	add	x0, x1, x0
 10c:	79405ba1 	ldrh	w1, [x29,#44]
 110:	d37ff821 	lsl	x1, x1, #1
 114:	f9400fa2 	ldr	x2, [x29,#24]
 118:	8b010041 	add	x1, x2, x1
 11c:	79400021 	ldrh	w1, [x1]
 120:	53087c21 	lsr	w1, w1, #8
 124:	53003c21 	uxth	w1, w1
 128:	53001c21 	uxtb	w1, w1
 12c:	39000001 	strb	w1, [x0]
 130:	79405fa0 	ldrh	w0, [x29,#46]
 134:	f94013a1 	ldr	x1, [x29,#32]
 138:	8b000020 	add	x0, x1, x0
 13c:	79405ba1 	ldrh	w1, [x29,#44]
 140:	d37ff821 	lsl	x1, x1, #1
 144:	f9400fa2 	ldr	x2, [x29,#24]
 148:	8b010041 	add	x1, x2, x1
 14c:	79400021 	ldrh	w1, [x1]
 150:	53001c21 	uxtb	w1, w1
 154:	39000001 	strb	w1, [x0]
 158:	79405fa0 	ldrh	w0, [x29,#46]
 15c:	11000800 	add	w0, w0, #0x2
 160:	79005fa0 	strh	w0, [x29,#46]
 164:	79405ba0 	ldrh	w0, [x29,#44]
 168:	51000400 	sub	w0, w0, #0x1
 16c:	79005ba0 	strh	w0, [x29,#44]
 170:	f9400ba0 	ldr	x0, [x29,#16]
 174:	79400000 	ldrh	w0, [x0]
 178:	79405fa1 	ldrh	w1, [x29,#46]
 17c:	6b00003f 	cmp	w1, w0
 180:	54fff8c3 	b.cc	98 <bytes_from_bignum+0x98>
 184:	f94013a0 	ldr	x0, [x29,#32]
 188:	a8c37bfd 	ldp	x29, x30, [sp],#48
 18c:	d65f03c0 	ret

Disassembly of section .text.modpow:

0000000000000000 <modpow>:
   0:	a9b87bfd 	stp	x29, x30, [sp,#-128]!
   4:	910003fd 	mov	x29, sp
   8:	f90017a0 	str	x0, [x29,#40]
   c:	f90013a1 	str	x1, [x29,#32]
  10:	f9000fa2 	str	x2, [x29,#24]
  14:	f9400fa0 	ldr	x0, [x29,#24]
  18:	79400000 	ldrh	w0, [x0]
  1c:	b90063a0 	str	w0, [x29,#96]
  20:	b98063a0 	ldrsw	x0, [x29,#96]
  24:	d37ff800 	lsl	x0, x0, #1
  28:	d2800201 	mov	x1, #0x10                  	// #16
  2c:	94000000 	bl	0 <NMemAlloc_align>
  30:	f9002fa0 	str	x0, [x29,#88]
  34:	b90067bf 	str	wzr, [x29,#100]
  38:	14000015 	b	8c <modpow+0x8c>
  3c:	f9400fa0 	ldr	x0, [x29,#24]
  40:	79400000 	ldrh	w0, [x0]
  44:	2a0003e1 	mov	w1, w0
  48:	b94067a0 	ldr	w0, [x29,#100]
  4c:	4b000020 	sub	w0, w1, w0
  50:	93407c00 	sxtw	x0, w0
  54:	d37ff800 	lsl	x0, x0, #1
  58:	f9400fa1 	ldr	x1, [x29,#24]
  5c:	8b000020 	add	x0, x1, x0
  60:	79400000 	ldrh	w0, [x0]
  64:	7900afa0 	strh	w0, [x29,#86]
  68:	b98067a0 	ldrsw	x0, [x29,#100]
  6c:	d37ff800 	lsl	x0, x0, #1
  70:	f9402fa1 	ldr	x1, [x29,#88]
  74:	8b000020 	add	x0, x1, x0
  78:	7940afa1 	ldrh	w1, [x29,#86]
  7c:	79000001 	strh	w1, [x0]
  80:	b94067a0 	ldr	w0, [x29,#100]
  84:	11000400 	add	w0, w0, #0x1
  88:	b90067a0 	str	w0, [x29,#100]
  8c:	b94067a1 	ldr	w1, [x29,#100]
  90:	b94063a0 	ldr	w0, [x29,#96]
  94:	6b00003f 	cmp	w1, w0
  98:	54fffd2b 	b.lt	3c <modpow+0x3c>
  9c:	b9006fbf 	str	wzr, [x29,#108]
  a0:	1400000d 	b	d4 <modpow+0xd4>
  a4:	f9402fa0 	ldr	x0, [x29,#88]
  a8:	79400000 	ldrh	w0, [x0]
  ac:	2a0003e1 	mov	w1, w0
  b0:	b9406fa0 	ldr	w0, [x29,#108]
  b4:	1ac02020 	lsl	w0, w1, w0
  b8:	12110000 	and	w0, w0, #0x8000
  bc:	6b1f001f 	cmp	w0, wzr
  c0:	54000040 	b.eq	c8 <modpow+0xc8>
  c4:	14000007 	b	e0 <modpow+0xe0>
  c8:	b9406fa0 	ldr	w0, [x29,#108]
  cc:	11000400 	add	w0, w0, #0x1
  d0:	b9006fa0 	str	w0, [x29,#108]
  d4:	b9406fa0 	ldr	w0, [x29,#108]
  d8:	7100381f 	cmp	w0, #0xe
  dc:	54fffe4d 	b.le	a4 <modpow+0xa4>
  e0:	b9406fa0 	ldr	w0, [x29,#108]
  e4:	6b1f001f 	cmp	w0, wzr
  e8:	54000700 	b.eq	1c8 <modpow+0x1c8>
  ec:	b9006bbf 	str	wzr, [x29,#104]
  f0:	14000021 	b	174 <modpow+0x174>
  f4:	b9806ba0 	ldrsw	x0, [x29,#104]
  f8:	d37ff800 	lsl	x0, x0, #1
  fc:	f9402fa1 	ldr	x1, [x29,#88]
 100:	8b000020 	add	x0, x1, x0
 104:	b9806ba1 	ldrsw	x1, [x29,#104]
 108:	d37ff821 	lsl	x1, x1, #1
 10c:	f9402fa2 	ldr	x2, [x29,#88]
 110:	8b010041 	add	x1, x2, x1
 114:	79400021 	ldrh	w1, [x1]
 118:	2a0103e2 	mov	w2, w1
 11c:	b9406fa1 	ldr	w1, [x29,#108]
 120:	1ac12041 	lsl	w1, w2, w1
 124:	13003c22 	sxth	w2, w1
 128:	b9806ba1 	ldrsw	x1, [x29,#104]
 12c:	91000421 	add	x1, x1, #0x1
 130:	d37ff821 	lsl	x1, x1, #1
 134:	f9402fa3 	ldr	x3, [x29,#88]
 138:	8b010061 	add	x1, x3, x1
 13c:	79400021 	ldrh	w1, [x1]
 140:	2a0103e4 	mov	w4, w1
 144:	52800203 	mov	w3, #0x10                  	// #16
 148:	b9406fa1 	ldr	w1, [x29,#108]
 14c:	4b010061 	sub	w1, w3, w1
 150:	1ac12881 	asr	w1, w4, w1
 154:	13003c21 	sxth	w1, w1
 158:	2a010041 	orr	w1, w2, w1
 15c:	13003c21 	sxth	w1, w1
 160:	53003c21 	uxth	w1, w1
 164:	79000001 	strh	w1, [x0]
 168:	b9406ba0 	ldr	w0, [x29,#104]
 16c:	11000400 	add	w0, w0, #0x1
 170:	b9006ba0 	str	w0, [x29,#104]
 174:	b94063a0 	ldr	w0, [x29,#96]
 178:	51000401 	sub	w1, w0, #0x1
 17c:	b9406ba0 	ldr	w0, [x29,#104]
 180:	6b00003f 	cmp	w1, w0
 184:	54fffb8c 	b.gt	f4 <modpow+0xf4>
 188:	b98063a0 	ldrsw	x0, [x29,#96]
 18c:	d37ff800 	lsl	x0, x0, #1
 190:	d1000800 	sub	x0, x0, #0x2
 194:	f9402fa1 	ldr	x1, [x29,#88]
 198:	8b000020 	add	x0, x1, x0
 19c:	b98063a1 	ldrsw	x1, [x29,#96]
 1a0:	d37ff821 	lsl	x1, x1, #1
 1a4:	d1000821 	sub	x1, x1, #0x2
 1a8:	f9402fa2 	ldr	x2, [x29,#88]
 1ac:	8b010041 	add	x1, x2, x1
 1b0:	79400021 	ldrh	w1, [x1]
 1b4:	2a0103e2 	mov	w2, w1
 1b8:	b9406fa1 	ldr	w1, [x29,#108]
 1bc:	1ac12041 	lsl	w1, w2, w1
 1c0:	53003c21 	uxth	w1, w1
 1c4:	79000001 	strh	w1, [x0]
 1c8:	b98063a0 	ldrsw	x0, [x29,#96]
 1cc:	d37ff800 	lsl	x0, x0, #1
 1d0:	d2800201 	mov	x1, #0x10                  	// #16
 1d4:	94000000 	bl	0 <NMemAlloc_align>
 1d8:	f90027a0 	str	x0, [x29,#72]
 1dc:	f94017a0 	ldr	x0, [x29,#40]
 1e0:	79400000 	ldrh	w0, [x0]
 1e4:	2a0003e1 	mov	w1, w0
 1e8:	b94063a0 	ldr	w0, [x29,#96]
 1ec:	4b010000 	sub	w0, w0, w1
 1f0:	b9006ba0 	str	w0, [x29,#104]
 1f4:	b90067bf 	str	wzr, [x29,#100]
 1f8:	14000009 	b	21c <modpow+0x21c>
 1fc:	b98067a0 	ldrsw	x0, [x29,#100]
 200:	d37ff800 	lsl	x0, x0, #1
 204:	f94027a1 	ldr	x1, [x29,#72]
 208:	8b000020 	add	x0, x1, x0
 20c:	7900001f 	strh	wzr, [x0]
 210:	b94067a0 	ldr	w0, [x29,#100]
 214:	11000400 	add	w0, w0, #0x1
 218:	b90067a0 	str	w0, [x29,#100]
 21c:	b94067a1 	ldr	w1, [x29,#100]
 220:	b9406ba0 	ldr	w0, [x29,#104]
 224:	6b00003f 	cmp	w1, w0
 228:	54fffeab 	b.lt	1fc <modpow+0x1fc>
 22c:	b90067bf 	str	wzr, [x29,#100]
 230:	14000016 	b	288 <modpow+0x288>
 234:	b9406ba1 	ldr	w1, [x29,#104]
 238:	b94067a0 	ldr	w0, [x29,#100]
 23c:	0b000020 	add	w0, w1, w0
 240:	93407c00 	sxtw	x0, w0
 244:	d37ff800 	lsl	x0, x0, #1
 248:	f94027a1 	ldr	x1, [x29,#72]
 24c:	8b000020 	add	x0, x1, x0
 250:	f94017a1 	ldr	x1, [x29,#40]
 254:	79400021 	ldrh	w1, [x1]
 258:	2a0103e2 	mov	w2, w1
 25c:	b94067a1 	ldr	w1, [x29,#100]
 260:	4b010041 	sub	w1, w2, w1
 264:	93407c21 	sxtw	x1, w1
 268:	d37ff821 	lsl	x1, x1, #1
 26c:	f94017a2 	ldr	x2, [x29,#40]
 270:	8b010041 	add	x1, x2, x1
 274:	79400021 	ldrh	w1, [x1]
 278:	79000001 	strh	w1, [x0]
 27c:	b94067a0 	ldr	w0, [x29,#100]
 280:	11000400 	add	w0, w0, #0x1
 284:	b90067a0 	str	w0, [x29,#100]
 288:	f94017a0 	ldr	x0, [x29,#40]
 28c:	79400000 	ldrh	w0, [x0]
 290:	2a0003e1 	mov	w1, w0
 294:	b94067a0 	ldr	w0, [x29,#100]
 298:	6b00003f 	cmp	w1, w0
 29c:	54fffccc 	b.gt	234 <modpow+0x234>
 2a0:	b98063a0 	ldrsw	x0, [x29,#96]
 2a4:	d37ef400 	lsl	x0, x0, #2
 2a8:	d2800201 	mov	x1, #0x10                  	// #16
 2ac:	94000000 	bl	0 <NMemAlloc_align>
 2b0:	f9003fa0 	str	x0, [x29,#120]
 2b4:	b98063a0 	ldrsw	x0, [x29,#96]
 2b8:	d37ef400 	lsl	x0, x0, #2
 2bc:	d2800201 	mov	x1, #0x10                  	// #16
 2c0:	94000000 	bl	0 <NMemAlloc_align>
 2c4:	f9003ba0 	str	x0, [x29,#112]
 2c8:	b9006bbf 	str	wzr, [x29,#104]
 2cc:	14000009 	b	2f0 <modpow+0x2f0>
 2d0:	b9806ba0 	ldrsw	x0, [x29,#104]
 2d4:	d37ff800 	lsl	x0, x0, #1
 2d8:	f9403fa1 	ldr	x1, [x29,#120]
 2dc:	8b000020 	add	x0, x1, x0
 2e0:	7900001f 	strh	wzr, [x0]
 2e4:	b9406ba0 	ldr	w0, [x29,#104]
 2e8:	11000400 	add	w0, w0, #0x1
 2ec:	b9006ba0 	str	w0, [x29,#104]
 2f0:	b94063a0 	ldr	w0, [x29,#96]
 2f4:	531f7801 	lsl	w1, w0, #1
 2f8:	b9406ba0 	ldr	w0, [x29,#104]
 2fc:	6b00003f 	cmp	w1, w0
 300:	54fffe8c 	b.gt	2d0 <modpow+0x2d0>
 304:	b98063a0 	ldrsw	x0, [x29,#96]
 308:	d37ef400 	lsl	x0, x0, #2
 30c:	d1000800 	sub	x0, x0, #0x2
 310:	f9403fa1 	ldr	x1, [x29,#120]
 314:	8b000020 	add	x0, x1, x0
 318:	52800021 	mov	w1, #0x1                   	// #1
 31c:	79000001 	strh	w1, [x0]
 320:	b9006bbf 	str	wzr, [x29,#104]
 324:	528001e0 	mov	w0, #0xf                   	// #15
 328:	b90067a0 	str	w0, [x29,#100]
 32c:	1400000c 	b	35c <modpow+0x35c>
 330:	b94067a0 	ldr	w0, [x29,#100]
 334:	51000400 	sub	w0, w0, #0x1
 338:	b90067a0 	str	w0, [x29,#100]
 33c:	b94067a0 	ldr	w0, [x29,#100]
 340:	6b1f001f 	cmp	w0, wzr
 344:	540000ca 	b.ge	35c <modpow+0x35c>
 348:	b9406ba0 	ldr	w0, [x29,#104]
 34c:	11000400 	add	w0, w0, #0x1
 350:	b9006ba0 	str	w0, [x29,#104]
 354:	528001e0 	mov	w0, #0xf                   	// #15
 358:	b90067a0 	str	w0, [x29,#100]
 35c:	f94013a0 	ldr	x0, [x29,#32]
 360:	79400000 	ldrh	w0, [x0]
 364:	2a0003e1 	mov	w1, w0
 368:	b9406ba0 	ldr	w0, [x29,#104]
 36c:	6b00003f 	cmp	w1, w0
 370:	5400022d 	b.le	3b4 <modpow+0x3b4>
 374:	f94013a0 	ldr	x0, [x29,#32]
 378:	79400000 	ldrh	w0, [x0]
 37c:	2a0003e1 	mov	w1, w0
 380:	b9406ba0 	ldr	w0, [x29,#104]
 384:	4b000020 	sub	w0, w1, w0
 388:	93407c00 	sxtw	x0, w0
 38c:	d37ff800 	lsl	x0, x0, #1
 390:	f94013a1 	ldr	x1, [x29,#32]
 394:	8b000020 	add	x0, x1, x0
 398:	79400000 	ldrh	w0, [x0]
 39c:	2a0003e1 	mov	w1, w0
 3a0:	b94067a0 	ldr	w0, [x29,#100]
 3a4:	1ac02820 	asr	w0, w1, w0
 3a8:	12000000 	and	w0, w0, #0x1
 3ac:	6b1f001f 	cmp	w0, wzr
 3b0:	54fffc00 	b.eq	330 <modpow+0x330>
 3b4:	1400004b 	b	4e0 <modpow+0x4e0>
 3b8:	14000042 	b	4c0 <modpow+0x4c0>
 3bc:	b98063a0 	ldrsw	x0, [x29,#96]
 3c0:	d37ff800 	lsl	x0, x0, #1
 3c4:	f9403fa1 	ldr	x1, [x29,#120]
 3c8:	8b000024 	add	x4, x1, x0
 3cc:	b98063a0 	ldrsw	x0, [x29,#96]
 3d0:	d37ff800 	lsl	x0, x0, #1
 3d4:	f9403fa1 	ldr	x1, [x29,#120]
 3d8:	8b000020 	add	x0, x1, x0
 3dc:	b94063a3 	ldr	w3, [x29,#96]
 3e0:	f9403ba2 	ldr	x2, [x29,#112]
 3e4:	aa0003e1 	mov	x1, x0
 3e8:	aa0403e0 	mov	x0, x4
 3ec:	94000000 	bl	0 <modpow>
 3f0:	b94063a0 	ldr	w0, [x29,#96]
 3f4:	531f7800 	lsl	w0, w0, #1
 3f8:	52800005 	mov	w5, #0x0                   	// #0
 3fc:	d2800004 	mov	x4, #0x0                   	// #0
 400:	b94063a3 	ldr	w3, [x29,#96]
 404:	f9402fa2 	ldr	x2, [x29,#88]
 408:	2a0003e1 	mov	w1, w0
 40c:	f9403ba0 	ldr	x0, [x29,#112]
 410:	94000000 	bl	0 <modpow>
 414:	f94013a0 	ldr	x0, [x29,#32]
 418:	79400000 	ldrh	w0, [x0]
 41c:	2a0003e1 	mov	w1, w0
 420:	b9406ba0 	ldr	w0, [x29,#104]
 424:	4b000020 	sub	w0, w1, w0
 428:	93407c00 	sxtw	x0, w0
 42c:	d37ff800 	lsl	x0, x0, #1
 430:	f94013a1 	ldr	x1, [x29,#32]
 434:	8b000020 	add	x0, x1, x0
 438:	79400000 	ldrh	w0, [x0]
 43c:	2a0003e1 	mov	w1, w0
 440:	b94067a0 	ldr	w0, [x29,#100]
 444:	1ac02820 	asr	w0, w1, w0
 448:	12000000 	and	w0, w0, #0x1
 44c:	6b1f001f 	cmp	w0, wzr
 450:	54000260 	b.eq	49c <modpow+0x49c>
 454:	b98063a0 	ldrsw	x0, [x29,#96]
 458:	d37ff800 	lsl	x0, x0, #1
 45c:	f9403ba1 	ldr	x1, [x29,#112]
 460:	8b000020 	add	x0, x1, x0
 464:	b94063a3 	ldr	w3, [x29,#96]
 468:	f9403fa2 	ldr	x2, [x29,#120]
 46c:	f94027a1 	ldr	x1, [x29,#72]
 470:	94000000 	bl	0 <modpow>
 474:	b94063a0 	ldr	w0, [x29,#96]
 478:	531f7800 	lsl	w0, w0, #1
 47c:	52800005 	mov	w5, #0x0                   	// #0
 480:	d2800004 	mov	x4, #0x0                   	// #0
 484:	b94063a3 	ldr	w3, [x29,#96]
 488:	f9402fa2 	ldr	x2, [x29,#88]
 48c:	2a0003e1 	mov	w1, w0
 490:	f9403fa0 	ldr	x0, [x29,#120]
 494:	94000000 	bl	0 <modpow>
 498:	14000007 	b	4b4 <modpow+0x4b4>
 49c:	f9403fa0 	ldr	x0, [x29,#120]
 4a0:	f90023a0 	str	x0, [x29,#64]
 4a4:	f9403ba0 	ldr	x0, [x29,#112]
 4a8:	f9003fa0 	str	x0, [x29,#120]
 4ac:	f94023a0 	ldr	x0, [x29,#64]
 4b0:	f9003ba0 	str	x0, [x29,#112]
 4b4:	b94067a0 	ldr	w0, [x29,#100]
 4b8:	51000400 	sub	w0, w0, #0x1
 4bc:	b90067a0 	str	w0, [x29,#100]
 4c0:	b94067a0 	ldr	w0, [x29,#100]
 4c4:	6b1f001f 	cmp	w0, wzr
 4c8:	54fff7aa 	b.ge	3bc <modpow+0x3bc>
 4cc:	b9406ba0 	ldr	w0, [x29,#104]
 4d0:	11000400 	add	w0, w0, #0x1
 4d4:	b9006ba0 	str	w0, [x29,#104]
 4d8:	528001e0 	mov	w0, #0xf                   	// #15
 4dc:	b90067a0 	str	w0, [x29,#100]
 4e0:	f94013a0 	ldr	x0, [x29,#32]
 4e4:	79400000 	ldrh	w0, [x0]
 4e8:	2a0003e1 	mov	w1, w0
 4ec:	b9406ba0 	ldr	w0, [x29,#104]
 4f0:	6b00003f 	cmp	w1, w0
 4f4:	54fff62c 	b.gt	3b8 <modpow+0x3b8>
 4f8:	b9406fa0 	ldr	w0, [x29,#108]
 4fc:	6b1f001f 	cmp	w0, wzr
 500:	54000da0 	b.eq	6b4 <modpow+0x6b4>
 504:	b94063a0 	ldr	w0, [x29,#96]
 508:	51000400 	sub	w0, w0, #0x1
 50c:	b9006ba0 	str	w0, [x29,#104]
 510:	14000021 	b	594 <modpow+0x594>
 514:	b9806ba0 	ldrsw	x0, [x29,#104]
 518:	d37ff800 	lsl	x0, x0, #1
 51c:	f9403fa1 	ldr	x1, [x29,#120]
 520:	8b000020 	add	x0, x1, x0
 524:	b9806ba1 	ldrsw	x1, [x29,#104]
 528:	d37ff821 	lsl	x1, x1, #1
 52c:	f9403fa2 	ldr	x2, [x29,#120]
 530:	8b010041 	add	x1, x2, x1
 534:	79400021 	ldrh	w1, [x1]
 538:	2a0103e2 	mov	w2, w1
 53c:	b9406fa1 	ldr	w1, [x29,#108]
 540:	1ac12041 	lsl	w1, w2, w1
 544:	13003c22 	sxth	w2, w1
 548:	b9806ba1 	ldrsw	x1, [x29,#104]
 54c:	91000421 	add	x1, x1, #0x1
 550:	d37ff821 	lsl	x1, x1, #1
 554:	f9403fa3 	ldr	x3, [x29,#120]
 558:	8b010061 	add	x1, x3, x1
 55c:	79400021 	ldrh	w1, [x1]
 560:	2a0103e4 	mov	w4, w1
 564:	52800203 	mov	w3, #0x10                  	// #16
 568:	b9406fa1 	ldr	w1, [x29,#108]
 56c:	4b010061 	sub	w1, w3, w1
 570:	1ac12881 	asr	w1, w4, w1
 574:	13003c21 	sxth	w1, w1
 578:	2a010041 	orr	w1, w2, w1
 57c:	13003c21 	sxth	w1, w1
 580:	53003c21 	uxth	w1, w1
 584:	79000001 	strh	w1, [x0]
 588:	b9406ba0 	ldr	w0, [x29,#104]
 58c:	11000400 	add	w0, w0, #0x1
 590:	b9006ba0 	str	w0, [x29,#104]
 594:	b94063a0 	ldr	w0, [x29,#96]
 598:	531f7800 	lsl	w0, w0, #1
 59c:	51000401 	sub	w1, w0, #0x1
 5a0:	b9406ba0 	ldr	w0, [x29,#104]
 5a4:	6b00003f 	cmp	w1, w0
 5a8:	54fffb6c 	b.gt	514 <modpow+0x514>
 5ac:	b98063a0 	ldrsw	x0, [x29,#96]
 5b0:	d37ef400 	lsl	x0, x0, #2
 5b4:	d1000800 	sub	x0, x0, #0x2
 5b8:	f9403fa1 	ldr	x1, [x29,#120]
 5bc:	8b000020 	add	x0, x1, x0
 5c0:	b98063a1 	ldrsw	x1, [x29,#96]
 5c4:	d37ef421 	lsl	x1, x1, #2
 5c8:	d1000821 	sub	x1, x1, #0x2
 5cc:	f9403fa2 	ldr	x2, [x29,#120]
 5d0:	8b010041 	add	x1, x2, x1
 5d4:	79400021 	ldrh	w1, [x1]
 5d8:	2a0103e2 	mov	w2, w1
 5dc:	b9406fa1 	ldr	w1, [x29,#108]
 5e0:	1ac12041 	lsl	w1, w2, w1
 5e4:	53003c21 	uxth	w1, w1
 5e8:	79000001 	strh	w1, [x0]
 5ec:	b94063a0 	ldr	w0, [x29,#96]
 5f0:	531f7800 	lsl	w0, w0, #1
 5f4:	52800005 	mov	w5, #0x0                   	// #0
 5f8:	d2800004 	mov	x4, #0x0                   	// #0
 5fc:	b94063a3 	ldr	w3, [x29,#96]
 600:	f9402fa2 	ldr	x2, [x29,#88]
 604:	2a0003e1 	mov	w1, w0
 608:	f9403fa0 	ldr	x0, [x29,#120]
 60c:	94000000 	bl	0 <modpow>
 610:	b94063a0 	ldr	w0, [x29,#96]
 614:	531f7800 	lsl	w0, w0, #1
 618:	51000400 	sub	w0, w0, #0x1
 61c:	b9006ba0 	str	w0, [x29,#104]
 620:	14000021 	b	6a4 <modpow+0x6a4>
 624:	b9806ba0 	ldrsw	x0, [x29,#104]
 628:	d37ff800 	lsl	x0, x0, #1
 62c:	f9403fa1 	ldr	x1, [x29,#120]
 630:	8b000020 	add	x0, x1, x0
 634:	b9806ba1 	ldrsw	x1, [x29,#104]
 638:	d37ff821 	lsl	x1, x1, #1
 63c:	f9403fa2 	ldr	x2, [x29,#120]
 640:	8b010041 	add	x1, x2, x1
 644:	79400021 	ldrh	w1, [x1]
 648:	2a0103e2 	mov	w2, w1
 64c:	b9406fa1 	ldr	w1, [x29,#108]
 650:	1ac12841 	asr	w1, w2, w1
 654:	13003c22 	sxth	w2, w1
 658:	b9806ba1 	ldrsw	x1, [x29,#104]
 65c:	d37ff821 	lsl	x1, x1, #1
 660:	d1000821 	sub	x1, x1, #0x2
 664:	f9403fa3 	ldr	x3, [x29,#120]
 668:	8b010061 	add	x1, x3, x1
 66c:	79400021 	ldrh	w1, [x1]
 670:	2a0103e4 	mov	w4, w1
 674:	52800203 	mov	w3, #0x10                  	// #16
 678:	b9406fa1 	ldr	w1, [x29,#108]
 67c:	4b010061 	sub	w1, w3, w1
 680:	1ac12081 	lsl	w1, w4, w1
 684:	13003c21 	sxth	w1, w1
 688:	2a010041 	orr	w1, w2, w1
 68c:	13003c21 	sxth	w1, w1
 690:	53003c21 	uxth	w1, w1
 694:	79000001 	strh	w1, [x0]
 698:	b9406ba0 	ldr	w0, [x29,#104]
 69c:	51000400 	sub	w0, w0, #0x1
 6a0:	b9006ba0 	str	w0, [x29,#104]
 6a4:	b9406ba1 	ldr	w1, [x29,#104]
 6a8:	b94063a0 	ldr	w0, [x29,#96]
 6ac:	6b00003f 	cmp	w1, w0
 6b0:	54fffbaa 	b.ge	624 <modpow+0x624>
 6b4:	f9400fa0 	ldr	x0, [x29,#24]
 6b8:	79400000 	ldrh	w0, [x0]
 6bc:	94000000 	bl	0 <modpow>
 6c0:	f9001fa0 	str	x0, [x29,#56]
 6c4:	b9006bbf 	str	wzr, [x29,#104]
 6c8:	14000016 	b	720 <modpow+0x720>
 6cc:	f9401fa0 	ldr	x0, [x29,#56]
 6d0:	79400000 	ldrh	w0, [x0]
 6d4:	2a0003e1 	mov	w1, w0
 6d8:	b9406ba0 	ldr	w0, [x29,#104]
 6dc:	4b000020 	sub	w0, w1, w0
 6e0:	93407c00 	sxtw	x0, w0
 6e4:	d37ff800 	lsl	x0, x0, #1
 6e8:	f9401fa1 	ldr	x1, [x29,#56]
 6ec:	8b000020 	add	x0, x1, x0
 6f0:	b9406ba2 	ldr	w2, [x29,#104]
 6f4:	b94063a1 	ldr	w1, [x29,#96]
 6f8:	0b010041 	add	w1, w2, w1
 6fc:	93407c21 	sxtw	x1, w1
 700:	d37ff821 	lsl	x1, x1, #1
 704:	f9403fa2 	ldr	x2, [x29,#120]
 708:	8b010041 	add	x1, x2, x1
 70c:	79400021 	ldrh	w1, [x1]
 710:	79000001 	strh	w1, [x0]
 714:	b9406ba0 	ldr	w0, [x29,#104]
 718:	11000400 	add	w0, w0, #0x1
 71c:	b9006ba0 	str	w0, [x29,#104]
 720:	b9406ba1 	ldr	w1, [x29,#104]
 724:	b94063a0 	ldr	w0, [x29,#96]
 728:	6b00003f 	cmp	w1, w0
 72c:	54fffd0b 	b.lt	6cc <modpow+0x6cc>
 730:	14000007 	b	74c <modpow+0x74c>
 734:	f9401fa0 	ldr	x0, [x29,#56]
 738:	79400000 	ldrh	w0, [x0]
 73c:	51000400 	sub	w0, w0, #0x1
 740:	53003c01 	uxth	w1, w0
 744:	f9401fa0 	ldr	x0, [x29,#56]
 748:	79000001 	strh	w1, [x0]
 74c:	f9401fa0 	ldr	x0, [x29,#56]
 750:	79400000 	ldrh	w0, [x0]
 754:	7100041f 	cmp	w0, #0x1
 758:	54000149 	b.ls	780 <modpow+0x780>
 75c:	f9401fa0 	ldr	x0, [x29,#56]
 760:	79400000 	ldrh	w0, [x0]
 764:	53003c00 	uxth	w0, w0
 768:	d37ff800 	lsl	x0, x0, #1
 76c:	f9401fa1 	ldr	x1, [x29,#56]
 770:	8b000020 	add	x0, x1, x0
 774:	79400000 	ldrh	w0, [x0]
 778:	6b1f001f 	cmp	w0, wzr
 77c:	54fffdc0 	b.eq	734 <modpow+0x734>
 780:	b9006bbf 	str	wzr, [x29,#104]
 784:	14000009 	b	7a8 <modpow+0x7a8>
 788:	b9806ba0 	ldrsw	x0, [x29,#104]
 78c:	d37ff800 	lsl	x0, x0, #1
 790:	f9403fa1 	ldr	x1, [x29,#120]
 794:	8b000020 	add	x0, x1, x0
 798:	7900001f 	strh	wzr, [x0]
 79c:	b9406ba0 	ldr	w0, [x29,#104]
 7a0:	11000400 	add	w0, w0, #0x1
 7a4:	b9006ba0 	str	w0, [x29,#104]
 7a8:	b94063a0 	ldr	w0, [x29,#96]
 7ac:	531f7801 	lsl	w1, w0, #1
 7b0:	b9406ba0 	ldr	w0, [x29,#104]
 7b4:	6b00003f 	cmp	w1, w0
 7b8:	54fffe8c 	b.gt	788 <modpow+0x788>
 7bc:	f9403fa0 	ldr	x0, [x29,#120]
 7c0:	94000000 	bl	0 <NMemFree>
 7c4:	b9006bbf 	str	wzr, [x29,#104]
 7c8:	14000009 	b	7ec <modpow+0x7ec>
 7cc:	b9806ba0 	ldrsw	x0, [x29,#104]
 7d0:	d37ff800 	lsl	x0, x0, #1
 7d4:	f9403ba1 	ldr	x1, [x29,#112]
 7d8:	8b000020 	add	x0, x1, x0
 7dc:	7900001f 	strh	wzr, [x0]
 7e0:	b9406ba0 	ldr	w0, [x29,#104]
 7e4:	11000400 	add	w0, w0, #0x1
 7e8:	b9006ba0 	str	w0, [x29,#104]
 7ec:	b94063a0 	ldr	w0, [x29,#96]
 7f0:	531f7801 	lsl	w1, w0, #1
 7f4:	b9406ba0 	ldr	w0, [x29,#104]
 7f8:	6b00003f 	cmp	w1, w0
 7fc:	54fffe8c 	b.gt	7cc <modpow+0x7cc>
 800:	f9403ba0 	ldr	x0, [x29,#112]
 804:	94000000 	bl	0 <NMemFree>
 808:	b9006bbf 	str	wzr, [x29,#104]
 80c:	14000009 	b	830 <modpow+0x830>
 810:	b9806ba0 	ldrsw	x0, [x29,#104]
 814:	d37ff800 	lsl	x0, x0, #1
 818:	f9402fa1 	ldr	x1, [x29,#88]
 81c:	8b000020 	add	x0, x1, x0
 820:	7900001f 	strh	wzr, [x0]
 824:	b9406ba0 	ldr	w0, [x29,#104]
 828:	11000400 	add	w0, w0, #0x1
 82c:	b9006ba0 	str	w0, [x29,#104]
 830:	b9406ba1 	ldr	w1, [x29,#104]
 834:	b94063a0 	ldr	w0, [x29,#96]
 838:	6b00003f 	cmp	w1, w0
 83c:	54fffeab 	b.lt	810 <modpow+0x810>
 840:	f9402fa0 	ldr	x0, [x29,#88]
 844:	94000000 	bl	0 <NMemFree>
 848:	b9006bbf 	str	wzr, [x29,#104]
 84c:	14000009 	b	870 <modpow+0x870>
 850:	b9806ba0 	ldrsw	x0, [x29,#104]
 854:	d37ff800 	lsl	x0, x0, #1
 858:	f94027a1 	ldr	x1, [x29,#72]
 85c:	8b000020 	add	x0, x1, x0
 860:	7900001f 	strh	wzr, [x0]
 864:	b9406ba0 	ldr	w0, [x29,#104]
 868:	11000400 	add	w0, w0, #0x1
 86c:	b9006ba0 	str	w0, [x29,#104]
 870:	b9406ba1 	ldr	w1, [x29,#104]
 874:	b94063a0 	ldr	w0, [x29,#96]
 878:	6b00003f 	cmp	w1, w0
 87c:	54fffeab 	b.lt	850 <modpow+0x850>
 880:	f94027a0 	ldr	x0, [x29,#72]
 884:	94000000 	bl	0 <NMemFree>
 888:	f9401fa0 	ldr	x0, [x29,#56]
 88c:	a8c87bfd 	ldp	x29, x30, [sp],#128
 890:	d65f03c0 	ret

Disassembly of section .debug_info:

0000000000000000 <.debug_info>:
   0:	00000510 	.inst	0x00000510 ; undefined
   4:	00000004 	.inst	0x00000004 ; undefined
   8:	01080000 	.inst	0x01080000 ; undefined
   c:	00000000 	.inst	0x00000000 ; undefined
  10:	00000001 	.inst	0x00000001 ; undefined
	...
  28:	05040200 	.inst	0x05040200 ; undefined
  2c:	00746e69 	.inst	0x00746e69 ; undefined
  30:	00080103 	.inst	0x00080103 ; undefined
  34:	03000000 	.inst	0x03000000 ; undefined
  38:	00000702 	.inst	0x00000702 ; undefined
  3c:	04030000 	.inst	0x04030000 ; undefined
  40:	00000007 	.inst	0x00000007 ; undefined
  44:	07080300 	.inst	0x07080300 ; undefined
  48:	00000000 	.inst	0x00000000 ; undefined
  4c:	00050803 	.inst	0x00050803 ; undefined
  50:	04000000 	.inst	0x04000000 ; undefined
  54:	00000000 	.inst	0x00000000 ; undefined
  58:	005e3802 	.inst	0x005e3802 ; undefined
  5c:	08050000 	stxrb	w5, w0, [x0]
  60:	00000037 	.inst	0x00000037 ; undefined
  64:	00000006 	.inst	0x00000006 ; undefined
  68:	00470100 	.inst	0x00470100 ; undefined
  6c:	00000000 	.inst	0x00000000 ; undefined
  70:	7c000000 	stur	h0, [x0]
  74:	00000001 	.inst	0x00000001 ; undefined
  78:	01000000 	.inst	0x01000000 ; undefined
  7c:	0000e59c 	.inst	0x0000e59c ; undefined
  80:	00610700 	.inst	0x00610700 ; undefined
  84:	005e4701 	.inst	0x005e4701 ; undefined
  88:	91020000 	add	x0, x0, #0x80
  8c:	00620758 	.inst	0x00620758 ; undefined
  90:	005e4701 	.inst	0x005e4701 ; undefined
  94:	91020000 	add	x0, x0, #0x80
  98:	00630750 	.inst	0x00630750 ; undefined
  9c:	005e4801 	.inst	0x005e4801 ; undefined
  a0:	91020000 	add	x0, x0, #0x80
  a4:	656c0748 	.inst	0x656c0748 ; undefined
  a8:	4801006e 	stxrh	w1, w14, [x3]
  ac:	00000029 	.inst	0x00000029 ; undefined
  b0:	08449102 	ldaxrb	w2, [x8]
  b4:	4a010069 	eor	w9, w3, w1
  b8:	00000029 	.inst	0x00000029 ; undefined
  bc:	087c9102 	.inst	0x087c9102 ; undefined
  c0:	4a01006a 	eor	w10, w3, w1
  c4:	00000029 	.inst	0x00000029 ; undefined
  c8:	08789102 	.inst	0x08789102 ; undefined
  cc:	01006961 	.inst	0x01006961 ; undefined
  d0:	0000e54b 	.inst	0x0000e54b ; undefined
  d4:	68910200 	.inst	0x68910200 ; undefined
  d8:	01007408 	.inst	0x01007408 ; undefined
  dc:	0000e54b 	.inst	0x0000e54b ; undefined
  e0:	70910200 	adr	x0, fffffffffff22123 <secure_bios_bignum_code+0xfffffffffff22093>
  e4:	07080300 	.inst	0x07080300 ; undefined
  e8:	00000000 	.inst	0x00000000 ; undefined
  ec:	00000006 	.inst	0x00000006 ; undefined
  f0:	005d0100 	.inst	0x005d0100 ; undefined
  f4:	00000000 	.inst	0x00000000 ; undefined
  f8:	cc000000 	.inst	0xcc000000 ; undefined
  fc:	00000000 	.inst	0x00000000 ; undefined
 100:	01000000 	.inst	0x01000000 ; undefined
 104:	00015c9c 	.inst	0x00015c9c ; undefined
 108:	00000900 	.inst	0x00000900 ; undefined
 10c:	5d010000 	.inst	0x5d010000 ; undefined
 110:	0000005e 	.inst	0x0000005e ; undefined
 114:	07589102 	.inst	0x07589102 ; undefined
 118:	5e01006e 	sha1c	q14, s3, v1.4s
 11c:	0000003e 	.inst	0x0000003e ; undefined
 120:	09549102 	.inst	0x09549102 ; undefined
 124:	00000000 	.inst	0x00000000 ; undefined
 128:	00295e01 	.inst	0x00295e01 ; NYI
 12c:	91020000 	add	x0, x0, #0x80
 130:	00000a50 	.inst	0x00000a50 ; undefined
 134:	60010000 	.inst	0x60010000 ; undefined
 138:	00000029 	.inst	0x00000029 ; undefined
 13c:	0a7c9102 	.inst	0x0a7c9102 ; undefined
 140:	00000000 	.inst	0x00000000 ; undefined
 144:	00296101 	.inst	0x00296101 ; NYI
 148:	91020000 	add	x0, x0, #0x80
 14c:	00000a6c 	.inst	0x00000a6c ; undefined
 150:	62010000 	.inst	0x62010000 ; undefined
 154:	000000e5 	.inst	0x000000e5 ; undefined
 158:	00709102 	.inst	0x00709102 ; undefined
 15c:	0000000b 	.inst	0x0000000b ; undefined
 160:	00780100 	.inst	0x00780100 ; undefined
 164:	00000000 	.inst	0x00000000 ; undefined
 168:	e8000000 	.inst	0xe8000000 ; undefined
 16c:	00000003 	.inst	0x00000003 ; undefined
 170:	01000000 	.inst	0x01000000 ; undefined
 174:	00025b9c 	.inst	0x00025b9c ; undefined
 178:	00610700 	.inst	0x00610700 ; undefined
 17c:	005e7801 	.inst	0x005e7801 ; undefined
 180:	91020000 	add	x0, x0, #0x80
 184:	00000948 	.inst	0x00000948 ; undefined
 188:	78010000 	sturh	w0, [x0,#16]
 18c:	00000029 	.inst	0x00000029 ; undefined
 190:	07449102 	.inst	0x07449102 ; undefined
 194:	7901006d 	strh	w13, [x3,#128]
 198:	0000005e 	.inst	0x0000005e ; undefined
 19c:	7fb89103 	fmulx	s3, s8, v24.s[1]
 1a0:	00000009 	.inst	0x00000009 ; undefined
 1a4:	29790100 	ldp	w0, w0, [x8,#-56]
 1a8:	02000000 	.inst	0x02000000 ; undefined
 1ac:	00094091 	.inst	0x00094091 ; undefined
 1b0:	01000000 	.inst	0x01000000 ; undefined
 1b4:	00005e7a 	.inst	0x00005e7a ; undefined
 1b8:	b0910300 	adrp	x0, ffffffff22061000 <secure_bios_bignum_code+0xffffffff22060f70>
 1bc:	0000097f 	.inst	0x0000097f ; undefined
 1c0:	7a010000 	sbcs	w0, w0, w1
 1c4:	00000029 	.inst	0x00000029 ; undefined
 1c8:	7fac9103 	fmulx	s3, s8, v12.s[1]
 1cc:	00306d08 	.inst	0x00306d08 ; NYI
 1d0:	00377c01 	.inst	0x00377c01 ; NYI
 1d4:	91020000 	add	x0, x0, #0x80
 1d8:	316d085a 	adds	w26, w2, #0xb42, lsl #12
 1dc:	377c0100 	tbnz	w0, #15, ffffffffffff81fc <secure_bios_bignum_code+0xffffffffffff816c>
 1e0:	02000000 	.inst	0x02000000 ; undefined
 1e4:	68087e91 	.inst	0x68087e91 ; undefined
 1e8:	3e7d0100 	.inst	0x3e7d0100 ; undefined
 1ec:	02000000 	.inst	0x02000000 ; undefined
 1f0:	69087891 	.inst	0x69087891 ; undefined
 1f4:	297e0100 	ldp	w0, w0, [x8,#-16]
 1f8:	02000000 	.inst	0x02000000 ; undefined
 1fc:	6b087491 	subs	w17, w4, w8, lsl #29
 200:	297e0100 	ldp	w0, w0, [x8,#-16]
 204:	02000000 	.inst	0x02000000 ; undefined
 208:	000c7091 	.inst	0x000c7091 ; undefined
 20c:	00000000 	.inst	0x00000000 ; undefined
 210:	68000000 	.inst	0x68000000 ; undefined
 214:	00000003 	.inst	0x00000003 ; undefined
 218:	08000000 	stxrb	w0, w0, [x0]
 21c:	87010074 	.inst	0x87010074 ; undefined
 220:	000000e5 	.inst	0x000000e5 ; undefined
 224:	08689102 	.inst	0x08689102 ; undefined
 228:	88010071 	stxr	w1, w17, [x3]
 22c:	0000003e 	.inst	0x0000003e ; undefined
 230:	08649102 	.inst	0x08649102 ; undefined
 234:	88010072 	stxr	w1, w18, [x3]
 238:	0000003e 	.inst	0x0000003e ; undefined
 23c:	08549102 	ldaxrb	w2, [x8]
 240:	88010063 	stxr	w1, w3, [x3]
 244:	0000003e 	.inst	0x0000003e ; undefined
 248:	08609102 	.inst	0x08609102 ; undefined
 24c:	00316961 	.inst	0x00316961 ; NYI
 250:	003e8801 	.inst	0x003e8801 ; NYI
 254:	91020000 	add	x0, x0, #0x80
 258:	0d00005c 	st1	{v28.b}[0], [x2]
 25c:	00000000 	.inst	0x00000000 ; undefined
 260:	0053c901 	.inst	0x0053c901 ; undefined
	...
 26c:	00780000 	.inst	0x00780000 ; undefined
 270:	00000000 	.inst	0x00000000 ; undefined
 274:	9c010000 	ldr	q0, 2274 <secure_bios_bignum_code+0x21e4>
 278:	00000297 	.inst	0x00000297 ; undefined
 27c:	00000009 	.inst	0x00000009 ; undefined
 280:	29c90100 	ldp	w0, w0, [x8,#72]!
 284:	02000000 	.inst	0x02000000 ; undefined
 288:	62086c91 	.inst	0x62086c91 ; undefined
 28c:	53cb0100 	.inst	0x53cb0100 ; undefined
 290:	02000000 	.inst	0x02000000 ; undefined
 294:	0e007891 	zip2	v17.8b, v4.8b, v0.8b
 298:	00000000 	.inst	0x00000000 ; undefined
 29c:	0000da01 	.inst	0x0000da01 ; undefined
 2a0:	00000000 	.inst	0x00000000 ; undefined
 2a4:	00400000 	.inst	0x00400000 ; undefined
 2a8:	00000000 	.inst	0x00000000 ; undefined
 2ac:	9c010000 	ldr	q0, 22ac <secure_bios_bignum_code+0x221c>
 2b0:	000002c1 	.inst	0x000002c1 ; undefined
 2b4:	01006207 	.inst	0x01006207 ; undefined
 2b8:	000053da 	.inst	0x000053da ; undefined
 2bc:	78910200 	ldrsh	x0, [x16,#-240]
 2c0:	00000d00 	.inst	0x00000d00 ; undefined
 2c4:	ec010000 	.inst	0xec010000 ; undefined
 2c8:	00000053 	.inst	0x00000053 ; undefined
	...
 2d4:	000001c0 	.inst	0x000001c0 ; undefined
 2d8:	00000000 	.inst	0x00000000 ; undefined
 2dc:	03459c01 	.inst	0x03459c01 ; undefined
 2e0:	00090000 	.inst	0x00090000 ; undefined
 2e4:	01000000 	.inst	0x01000000 ; undefined
 2e8:	000345ec 	.inst	0x000345ec ; undefined
 2ec:	58910200 	ldr	x0, fffffffffff2232c <secure_bios_bignum_code+0xfffffffffff2229c>
 2f0:	00000009 	.inst	0x00000009 ; undefined
 2f4:	29ec0100 	ldp	w0, w0, [x8,#-160]!
 2f8:	02000000 	.inst	0x02000000 ; undefined
 2fc:	000a5491 	.inst	0x000a5491 ; undefined
 300:	01000000 	.inst	0x01000000 ; undefined
 304:	000053ee 	.inst	0x000053ee ; undefined
 308:	70910200 	adr	x0, fffffffffff2234b <secure_bios_bignum_code+0xfffffffffff222bb>
 30c:	01007708 	.inst	0x01007708 ; undefined
 310:	000029ef 	.inst	0x000029ef ; undefined
 314:	78910200 	ldrsh	x0, [x16,#-240]
 318:	01006908 	.inst	0x01006908 ; undefined
 31c:	000029ef 	.inst	0x000029ef ; undefined
 320:	7c910200 	.inst	0x7c910200 ; undefined
 324:	0000000c 	.inst	0x0000000c ; undefined
 328:	00000000 	.inst	0x00000000 ; undefined
 32c:	0000d400 	.inst	0x0000d400 ; undefined
 330:	00000000 	.inst	0x00000000 ; undefined
 334:	00000a00 	.inst	0x00000a00 ; undefined
 338:	f7010000 	.inst	0xf7010000 ; undefined
 33c:	00000030 	.inst	0x00000030 ; undefined
 340:	006f9102 	.inst	0x006f9102 ; undefined
 344:	4b080500 	sub	w0, w8, w8, lsl #1
 348:	0f000003 	.inst	0x0f000003 ; undefined
 34c:	00000030 	.inst	0x00000030 ; undefined
 350:	00000010 	.inst	0x00000010 ; undefined
 354:	010d0100 	.inst	0x010d0100 ; undefined
 358:	000003c8 	.inst	0x000003c8 ; undefined
	...
 364:	00000190 	.inst	0x00000190 ; undefined
 368:	00000000 	.inst	0x00000000 ; undefined
 36c:	03c89c01 	.inst	0x03c89c01 ; undefined
 370:	62110000 	.inst	0x62110000 ; undefined
 374:	0d01006e 	.inst	0x0d01006e ; undefined
 378:	00005301 	.inst	0x00005301 ; undefined
 37c:	68910200 	.inst	0x68910200 ; undefined
 380:	00000012 	.inst	0x00000012 ; undefined
 384:	010d0100 	.inst	0x010d0100 ; undefined
 388:	0000005e 	.inst	0x0000005e ; undefined
 38c:	13609102 	.inst	0x13609102 ; undefined
 390:	0f010069 	.inst	0x0f010069 ; undefined
 394:	00003701 	.inst	0x00003701 ; undefined
 398:	7e910200 	.inst	0x7e910200 ; undefined
 39c:	01006a13 	.inst	0x01006a13 ; undefined
 3a0:	0037010f 	.inst	0x0037010f ; NYI
 3a4:	91020000 	add	x0, x0, #0x80
 3a8:	0000147c 	.inst	0x0000147c ; undefined
 3ac:	10010000 	adr	x0, 23ac <secure_bios_bignum_code+0x231c>
 3b0:	00003701 	.inst	0x00003701 ; undefined
 3b4:	7a910200 	.inst	0x7a910200 ; undefined
 3b8:	00000014 	.inst	0x00000014 ; undefined
 3bc:	01110100 	.inst	0x01110100 ; undefined
 3c0:	000003c8 	.inst	0x000003c8 ; undefined
 3c4:	00709102 	.inst	0x00709102 ; undefined
 3c8:	00300805 	.inst	0x00300805 ; NYI
 3cc:	00100000 	.inst	0x00100000 ; undefined
 3d0:	01000000 	.inst	0x01000000 ; undefined
 3d4:	00530141 	.inst	0x00530141 ; undefined
	...
 3e0:	08940000 	.inst	0x08940000 ; undefined
 3e4:	00000000 	.inst	0x00000000 ; undefined
 3e8:	9c010000 	ldr	q0, 23e8 <secure_bios_bignum_code+0x2358>
 3ec:	000004cb 	.inst	0x000004cb ; undefined
 3f0:	00000012 	.inst	0x00000012 ; undefined
 3f4:	01410100 	.inst	0x01410100 ; undefined
 3f8:	00000053 	.inst	0x00000053 ; undefined
 3fc:	7fa89103 	fmulx	s3, s8, v8.s[1]
 400:	70786511 	adr	x17, f10a3 <secure_bios_bignum_code+0xf1013>
 404:	01410100 	.inst	0x01410100 ; undefined
 408:	00000053 	.inst	0x00000053 ; undefined
 40c:	7fa09103 	fmulx	s3, s8, v0.s[1]
 410:	646f6d11 	.inst	0x646f6d11 ; undefined
 414:	01410100 	.inst	0x01410100 ; undefined
 418:	00000053 	.inst	0x00000053 ; undefined
 41c:	7f989103 	fmulx	s3, s8, v24.s[0]
 420:	01006113 	.inst	0x01006113 ; undefined
 424:	005e0143 	.inst	0x005e0143 ; undefined
 428:	91020000 	add	x0, x0, #0x80
 42c:	00621378 	.inst	0x00621378 ; undefined
 430:	5e014301 	sha256h	q1, q24, v1.4s
 434:	02000000 	.inst	0x02000000 ; undefined
 438:	6e137091 	.inst	0x6e137091 ; undefined
 43c:	01430100 	.inst	0x01430100 ; undefined
 440:	0000005e 	.inst	0x0000005e ; undefined
 444:	13489102 	.inst	0x13489102 ; undefined
 448:	4301006d 	.inst	0x4301006d ; undefined
 44c:	00005e01 	.inst	0x00005e01 ; undefined
 450:	58910200 	ldr	x0, fffffffffff22490 <secure_bios_bignum_code+0xfffffffffff22400>
 454:	00000014 	.inst	0x00000014 ; undefined
 458:	01430100 	.inst	0x01430100 ; undefined
 45c:	00000037 	.inst	0x00000037 ; undefined
 460:	14569102 	b	15a4868 <secure_bios_bignum_code+0x15a47d8>
 464:	00000000 	.inst	0x00000000 ; undefined
 468:	29014401 	stp	w1, w17, [x0,#8]
 46c:	02000000 	.inst	0x02000000 ; undefined
 470:	00146c91 	.inst	0x00146c91 ; undefined
 474:	01000000 	.inst	0x01000000 ; undefined
 478:	00290145 	.inst	0x00290145 ; NYI
 47c:	91020000 	add	x0, x0, #0x80
 480:	00691360 	.inst	0x00691360 ; undefined
 484:	29014501 	stp	w1, w17, [x8,#8]
 488:	02000000 	.inst	0x02000000 ; undefined
 48c:	6a136891 	ands	w17, w4, w19, lsl #26
 490:	01450100 	.inst	0x01450100 ; undefined
 494:	00000029 	.inst	0x00000029 ; undefined
 498:	14649102 	b	19248a0 <secure_bios_bignum_code+0x1924810>
 49c:	00000000 	.inst	0x00000000 ; undefined
 4a0:	53014601 	ubfx	w1, w16, #1, #17
 4a4:	03000000 	.inst	0x03000000 ; undefined
 4a8:	0c7fb891 	.inst	0x0c7fb891 ; undefined
	...
 4b4:	00000018 	.inst	0x00000018 ; undefined
 4b8:	00000000 	.inst	0x00000000 ; undefined
 4bc:	01007413 	.inst	0x01007413 ; undefined
 4c0:	005e017e 	.inst	0x005e017e ; undefined
 4c4:	91020000 	add	x0, x0, #0x80
 4c8:	15000040 	b	40005c8 <secure_bios_bignum_code+0x4000538>
 4cc:	000004e2 	.inst	0x000004e2 ; undefined
 4d0:	000004db 	.inst	0x000004db ; undefined
 4d4:	0004db16 	.inst	0x0004db16 ; undefined
 4d8:	03008c00 	.inst	0x03008c00 ; undefined
 4dc:	00000708 	.inst	0x00000708 ; undefined
 4e0:	01030000 	.inst	0x01030000 ; undefined
 4e4:	00000008 	.inst	0x00000008 ; undefined
 4e8:	00001700 	.inst	0x00001700 ; undefined
 4ec:	38010000 	sturb	w0, [x0,#16]
 4f0:	000004cb 	.inst	0x000004cb ; undefined
 4f4:	00000309 	.inst	0x00000309 ; undefined
 4f8:	00000000 	.inst	0x00000000 ; undefined
 4fc:	00170000 	.inst	0x00170000 ; undefined
 500:	01000000 	.inst	0x01000000 ; undefined
 504:	0004cb39 	.inst	0x0004cb39 ; undefined
 508:	00030900 	.inst	0x00030900 ; undefined
	...

Disassembly of section .debug_abbrev:

0000000000000000 <.debug_abbrev>:
   0:	25011101 	.inst	0x25011101 ; undefined
   4:	030b130e 	.inst	0x030b130e ; undefined
   8:	550e1b0e 	.inst	0x550e1b0e ; undefined
   c:	10011117 	adr	x23, 222c <secure_bios_bignum_code+0x219c>
  10:	02000017 	.inst	0x02000017 ; undefined
  14:	0b0b0024 	add	w4, w1, w11
  18:	08030b3e 	stxrb	w3, w30, [x25]
  1c:	24030000 	.inst	0x24030000 ; undefined
  20:	3e0b0b00 	.inst	0x3e0b0b00 ; undefined
  24:	000e030b 	.inst	0x000e030b ; undefined
  28:	00160400 	.inst	0x00160400 ; undefined
  2c:	0b3a0e03 	add	w3, w16, w26, uxtb #3
  30:	13490b3b 	.inst	0x13490b3b ; undefined
  34:	0f050000 	.inst	0x0f050000 ; undefined
  38:	490b0b00 	.inst	0x490b0b00 ; undefined
  3c:	06000013 	.inst	0x06000013 ; undefined
  40:	0e03012e 	tbl	v14.8b, {v9.16b}, v3.8b
  44:	0b3b0b3a 	add	w26, w25, w27, uxtb #2
  48:	01111927 	.inst	0x01111927 ; undefined
  4c:	18400712 	ldr	w18, 8012c <secure_bios_bignum_code+0x8009c>
  50:	01194297 	.inst	0x01194297 ; undefined
  54:	07000013 	.inst	0x07000013 ; undefined
  58:	08030005 	stxrb	w3, w5, [x0]
  5c:	0b3b0b3a 	add	w26, w25, w27, uxtb #2
  60:	18021349 	ldr	w9, 42c8 <secure_bios_bignum_code+0x4238>
  64:	34080000 	cbz	w0, 10064 <secure_bios_bignum_code+0xffd4>
  68:	3a080300 	adcs	w0, w24, w8
  6c:	490b3b0b 	.inst	0x490b3b0b ; undefined
  70:	00180213 	.inst	0x00180213 ; undefined
  74:	00050900 	.inst	0x00050900 ; undefined
  78:	0b3a0e03 	add	w3, w16, w26, uxtb #3
  7c:	13490b3b 	.inst	0x13490b3b ; undefined
  80:	00001802 	.inst	0x00001802 ; undefined
  84:	0300340a 	.inst	0x0300340a ; undefined
  88:	3b0b3a0e 	.inst	0x3b0b3a0e ; undefined
  8c:	0213490b 	.inst	0x0213490b ; undefined
  90:	0b000018 	add	w24, w0, w0
  94:	0e03012e 	tbl	v14.8b, {v9.16b}, v3.8b
  98:	0b3b0b3a 	add	w26, w25, w27, uxtb #2
  9c:	01111927 	.inst	0x01111927 ; undefined
  a0:	18400712 	ldr	w18, 80180 <secure_bios_bignum_code+0x800f0>
  a4:	01194296 	.inst	0x01194296 ; undefined
  a8:	0c000013 	st4	{v19.8b-v22.8b}, [x0]
  ac:	0111010b 	.inst	0x0111010b ; undefined
  b0:	00000712 	.inst	0x00000712 ; undefined
  b4:	3f012e0d 	.inst	0x3f012e0d ; undefined
  b8:	3a0e0319 	adcs	w25, w24, w14
  bc:	270b3b0b 	.inst	0x270b3b0b ; undefined
  c0:	11134919 	add	w25, w8, #0x4d2
  c4:	40071201 	.inst	0x40071201 ; undefined
  c8:	19429618 	.inst	0x19429618 ; undefined
  cc:	00001301 	.inst	0x00001301 ; undefined
  d0:	3f012e0e 	.inst	0x3f012e0e ; undefined
  d4:	3a0e0319 	adcs	w25, w24, w14
  d8:	270b3b0b 	.inst	0x270b3b0b ; undefined
  dc:	12011119 	and	w25, w8, #0x8000000f
  e0:	96184007 	bl	fffffffff86100fc <secure_bios_bignum_code+0xfffffffff861006c>
  e4:	13011942 	sbfx	w2, w10, #1, #6
  e8:	260f0000 	.inst	0x260f0000 ; undefined
  ec:	00134900 	.inst	0x00134900 ; undefined
  f0:	012e1000 	.inst	0x012e1000 ; undefined
  f4:	0e03193f 	uzp1	v31.8b, v9.8b, v3.8b
  f8:	053b0b3a 	.inst	0x053b0b3a ; undefined
  fc:	13491927 	.inst	0x13491927 ; undefined
 100:	07120111 	.inst	0x07120111 ; undefined
 104:	42961840 	.inst	0x42961840 ; undefined
 108:	00130119 	.inst	0x00130119 ; undefined
 10c:	00051100 	.inst	0x00051100 ; undefined
 110:	0b3a0803 	add	w3, w0, w26, uxtb #2
 114:	1349053b 	.inst	0x1349053b ; undefined
 118:	00001802 	.inst	0x00001802 ; undefined
 11c:	03000512 	.inst	0x03000512 ; undefined
 120:	3b0b3a0e 	.inst	0x3b0b3a0e ; undefined
 124:	02134905 	.inst	0x02134905 ; undefined
 128:	13000018 	sbfx	w24, w0, #0, #1
 12c:	08030034 	stxrb	w3, w20, [x1]
 130:	053b0b3a 	.inst	0x053b0b3a ; undefined
 134:	18021349 	ldr	w9, 439c <secure_bios_bignum_code+0x430c>
 138:	34140000 	cbz	w0, 28138 <secure_bios_bignum_code+0x280a8>
 13c:	3a0e0300 	adcs	w0, w24, w14
 140:	49053b0b 	.inst	0x49053b0b ; undefined
 144:	00180213 	.inst	0x00180213 ; undefined
 148:	01011500 	.inst	0x01011500 ; undefined
 14c:	13011349 	sbfx	w9, w26, #1, #4
 150:	21160000 	.inst	0x21160000 ; undefined
 154:	2f134900 	.inst	0x2f134900 ; undefined
 158:	1700000b 	b	fffffffffc000184 <secure_bios_bignum_code+0xfffffffffc0000f4>
 15c:	0e030034 	tbl	v20.8b, {v1.16b}, v3.8b
 160:	0b3b0b3a 	add	w26, w25, w27, uxtb #2
 164:	193f1349 	.inst	0x193f1349 ; undefined
 168:	00001802 	.inst	0x00001802 ; undefined
	...

Disassembly of section .debug_aranges:

0000000000000000 <.debug_aranges>:
   0:	0000009c 	.inst	0x0000009c ; undefined
   4:	00000002 	.inst	0x00000002 ; undefined
   8:	00080000 	.inst	0x00080000 ; undefined
	...
  18:	0000017c 	.inst	0x0000017c ; undefined
	...
  28:	000000cc 	.inst	0x000000cc ; undefined
	...
  38:	000003e8 	.inst	0x000003e8 ; undefined
	...
  48:	00000078 	.inst	0x00000078 ; undefined
	...
  58:	00000040 	.inst	0x00000040 ; undefined
	...
  68:	000001c0 	.inst	0x000001c0 ; undefined
	...
  78:	00000190 	.inst	0x00000190 ; undefined
	...
  88:	00000894 	.inst	0x00000894 ; undefined
	...

Disassembly of section .debug_ranges:

0000000000000000 <.debug_ranges>:
	...

Disassembly of section .debug_line:

0000000000000000 <.debug_line>:
   0:	0000034d 	.inst	0x0000034d ; undefined
   4:	002b0002 	.inst	0x002b0002 ; NYI
   8:	01020000 	.inst	0x01020000 ; undefined
   c:	000d0efb 	.inst	0x000d0efb ; undefined
  10:	01010101 	.inst	0x01010101 ; undefined
  14:	01000000 	.inst	0x01000000 ; undefined
  18:	00010000 	.inst	0x00010000 ; undefined
  1c:	6e676962 	.inst	0x6e676962 ; undefined
  20:	632e6d75 	.inst	0x632e6d75 ; undefined
  24:	00000000 	.inst	0x00000000 ; undefined
  28:	6e676962 	.inst	0x6e676962 ; undefined
  2c:	682e6d75 	.inst	0x682e6d75 ; undefined
  30:	00000000 	.inst	0x00000000 ; undefined
  34:	02090000 	.inst	0x02090000 ; undefined
	...
  40:	0100c803 	.inst	0x0100c803 ; undefined
  44:	040200a2 	.inst	0x040200a2 ; undefined
  48:	02004b03 	.inst	0x02004b03 ; undefined
  4c:	009d0304 	.inst	0x009d0304 ; undefined
  50:	06010402 	.inst	0x06010402 ; undefined
  54:	83a10666 	.inst	0x83a10666 ; undefined
  58:	02002fd7 	.inst	0x02002fd7 ; undefined
  5c:	00830304 	.inst	0x00830304 ; undefined
  60:	08030402 	stxrb	w3, w2, [x0]
  64:	04020059 	.inst	0x04020059 ; undefined
  68:	00910803 	.inst	0x00910803 ; undefined
  6c:	08030402 	stxrb	w3, w2, [x0]
  70:	04020059 	.inst	0x04020059 ; undefined
  74:	02006203 	.inst	0x02006203 ; undefined
  78:	66060104 	.inst	0x66060104 ; undefined
  7c:	02040200 	.inst	0x02040200 ; undefined
  80:	02006c06 	.inst	0x02006c06 ; undefined
  84:	77030204 	.inst	0x77030204 ; undefined
  88:	040200d6 	.inst	0x040200d6 ; undefined
  8c:	06660601 	.inst	0x06660601 ; undefined
  90:	02660b03 	.inst	0x02660b03 ; undefined
  94:	01010004 	.inst	0x01010004 ; undefined
  98:	00020900 	.inst	0x00020900 ; undefined
  9c:	00000000 	.inst	0x00000000 ; undefined
  a0:	03000000 	.inst	0x03000000 ; undefined
  a4:	830100de 	.inst	0x830100de ; undefined
  a8:	2fa0d9d7 	.inst	0x2fa0d9d7 ; undefined
  ac:	67d72108 	.inst	0x67d72108 ; undefined
  b0:	04026c62 	.inst	0x04026c62 ; undefined
  b4:	00010100 	.inst	0x00010100 ; undefined
  b8:	00000209 	.inst	0x00000209 ; undefined
  bc:	00000000 	.inst	0x00000000 ; undefined
  c0:	fa030000 	sbcs	x0, x0, x3
  c4:	67f70100 	.inst	0x67f70100 ; undefined
  c8:	4e308467 	add	v7.16b, v3.16b, v16.16b
  cc:	bdd74c67 	.inst	0xbdd74c67 ; undefined
  d0:	08d94c9f 	.inst	0x08d94c9f ; undefined
  d4:	83be833d 	.inst	0x83be833d ; undefined
  d8:	9f8367d7 	.inst	0x9f8367d7 ; undefined
  dc:	01040200 	.inst	0x01040200 ; undefined
  e0:	04020083 	.inst	0x04020083 ; undefined
  e4:	6a678101 	.inst	0x6a678101 ; undefined
  e8:	2108832f 	.inst	0x2108832f ; undefined
  ec:	75086783 	.inst	0x75086783 ; undefined
  f0:	02040200 	.inst	0x02040200 ; undefined
  f4:	04020067 	.inst	0x04020067 ; undefined
  f8:	027a0302 	.inst	0x027a0302 ; undefined
  fc:	02000128 	.inst	0x02000128 ; undefined
 100:	66060104 	.inst	0x66060104 ; undefined
 104:	660a0306 	.inst	0x660a0306 ; undefined
 108:	02002f83 	.inst	0x02002f83 ; undefined
 10c:	00830304 	.inst	0x00830304 ; undefined
 110:	08030402 	stxrb	w3, w2, [x0]
 114:	04020021 	.inst	0x04020021 ; undefined
 118:	00750803 	.inst	0x00750803 ; undefined
 11c:	08030402 	stxrb	w3, w2, [x0]
 120:	0402003d 	.inst	0x0402003d ; undefined
 124:	02006203 	.inst	0x02006203 ; undefined
 128:	66060104 	.inst	0x66060104 ; undefined
 12c:	67686c06 	.inst	0x67686c06 ; undefined
 130:	02040200 	.inst	0x02040200 ; undefined
 134:	74084903 	.inst	0x74084903 ; undefined
 138:	01040200 	.inst	0x01040200 ; undefined
 13c:	03066606 	.inst	0x03066606 ; undefined
 140:	0402ba39 	.inst	0x0402ba39 ; undefined
 144:	00010100 	.inst	0x00010100 ; undefined
 148:	00000209 	.inst	0x00000209 ; undefined
 14c:	00000000 	.inst	0x00000000 ; undefined
 150:	c9030000 	.inst	0xc9030000 ; undefined
 154:	d7670101 	.inst	0xd7670101 ; undefined
 158:	83f34b67 	.inst	0x83f34b67 ; undefined
 15c:	0004022f 	.inst	0x0004022f ; undefined
 160:	09000101 	.inst	0x09000101 ; undefined
 164:	00000002 	.inst	0x00000002 ; undefined
 168:	00000000 	.inst	0x00000000 ; undefined
 16c:	01da0300 	.inst	0x01da0300 ; undefined
 170:	21086a01 	.inst	0x21086a01 ; undefined
 174:	0004024b 	.inst	0x0004024b ; undefined
 178:	09000101 	.inst	0x09000101 ; undefined
 17c:	00000002 	.inst	0x00000002 ; undefined
 180:	00000000 	.inst	0x00000000 ; undefined
 184:	01ec0300 	.inst	0x01ec0300 ; undefined
 188:	67bc8601 	.inst	0x67bc8601 ; undefined
 18c:	03040200 	.inst	0x03040200 ; undefined
 190:	04020067 	.inst	0x04020067 ; undefined
 194:	02009d03 	.inst	0x02009d03 ; undefined
 198:	66060104 	.inst	0x66060104 ; undefined
 19c:	9f678406 	.inst	0x9f678406 ; undefined
 1a0:	14300283 	b	c00bac <secure_bios_bignum_code+0xc00b1c>
 1a4:	01040200 	.inst	0x01040200 ; undefined
 1a8:	a60d2802 	.inst	0xa60d2802 ; undefined
 1ac:	0200b92f 	.inst	0x0200b92f ; undefined
 1b0:	82060104 	.inst	0x82060104 ; undefined
 1b4:	2f220806 	.inst	0x2f220806 ; undefined
 1b8:	01000402 	.inst	0x01000402 ; undefined
 1bc:	02090001 	.inst	0x02090001 ; undefined
	...
 1c8:	01028d03 	.inst	0x01028d03 ; undefined
 1cc:	f4d76988 	.inst	0xf4d76988 ; undefined
 1d0:	00a1c0a1 	.inst	0x00a1c0a1 ; undefined
 1d4:	06010402 	.inst	0x06010402 ; undefined
 1d8:	08d80666 	.inst	0x08d80666 ; undefined
 1dc:	91088659 	add	x25, x18, #0x221
 1e0:	02040200 	.inst	0x02040200 ; undefined
 1e4:	3c087503 	str	b3, [x8],#135
 1e8:	01040200 	.inst	0x01040200 ; undefined
 1ec:	0306ba06 	.inst	0x0306ba06 ; undefined
 1f0:	022f9e0f 	.inst	0x022f9e0f ; undefined
 1f4:	01010004 	.inst	0x01010004 ; undefined
 1f8:	00020900 	.inst	0x00020900 ; undefined
 1fc:	00000000 	.inst	0x00000000 ; undefined
 200:	03000000 	.inst	0x03000000 ; undefined
 204:	a60102c1 	.inst	0xa60102c1 ; undefined
 208:	02009f67 	.inst	0x02009f67 ; undefined
 20c:	004b0304 	.inst	0x004b0304 ; undefined
 210:	08030402 	stxrb	w3, w2, [x0]
 214:	04020059 	.inst	0x04020059 ; undefined
 218:	0200b803 	.inst	0x0200b803 ; undefined
 21c:	66060104 	.inst	0x66060104 ; undefined
 220:	f34b8806 	.inst	0xf34b8806 ; undefined
 224:	02040200 	.inst	0x02040200 ; undefined
 228:	0402002c 	.inst	0x0402002c ; undefined
 22c:	06660601 	.inst	0x06660601 ; undefined
 230:	02006769 	.inst	0x02006769 ; undefined
 234:	004b0304 	.inst	0x004b0304 ; undefined
 238:	02030402 	.inst	0x02030402 ; undefined
 23c:	0200113a 	.inst	0x0200113a ; undefined
 240:	66060104 	.inst	0x66060104 ; undefined
 244:	e808a006 	.inst	0xe808a006 ; undefined
 248:	0200bb9f 	.inst	0x0200bb9f ; undefined
 24c:	004b0304 	.inst	0x004b0304 ; undefined
 250:	9d030402 	.inst	0x9d030402 ; undefined
 254:	01040200 	.inst	0x01040200 ; undefined
 258:	84066606 	.inst	0x84066606 ; undefined
 25c:	03040200 	.inst	0x03040200 ; undefined
 260:	0402004b 	.inst	0x0402004b ; undefined
 264:	11240203 	add	w3, w16, #0x900
 268:	01040200 	.inst	0x01040200 ; undefined
 26c:	be066606 	.inst	0xbe066606 ; undefined
 270:	02009f9f 	.inst	0x02009f9f ; undefined
 274:	004b0304 	.inst	0x004b0304 ; undefined
 278:	9d030402 	.inst	0x9d030402 ; undefined
 27c:	01040200 	.inst	0x01040200 ; undefined
 280:	a0066606 	.inst	0xa0066606 ; undefined
 284:	2f4b2fd9 	.inst	0x2f4b2fd9 ; undefined
 288:	46676767 	.inst	0x46676767 ; undefined
 28c:	01040200 	.inst	0x01040200 ; undefined
 290:	0306ba06 	.inst	0x0306ba06 ; undefined
 294:	2fe40809 	.inst	0x2fe40809 ; undefined
 298:	0891082f 	.inst	0x0891082f ; undefined
 29c:	f3e50821 	.inst	0xf3e50821 ; undefined
 2a0:	4b4b3f08 	sub	w8, w24, w11, lsr #15
 2a4:	6674034c 	.inst	0x6674034c ; undefined
 2a8:	67660e03 	.inst	0x67660e03 ; undefined
 2ac:	034a7003 	.inst	0x034a7003 ; undefined
 2b0:	0067ba14 	.inst	0x0067ba14 ; undefined
 2b4:	83030402 	.inst	0x83030402 ; undefined
 2b8:	03040200 	.inst	0x03040200 ; undefined
 2bc:	00113a02 	.inst	0x00113a02 ; undefined
 2c0:	06010402 	.inst	0x06010402 ; undefined
 2c4:	08bc0666 	.inst	0x08bc0666 ; undefined
 2c8:	002108e5 	.inst	0x002108e5 ; NYI
 2cc:	9f030402 	.inst	0x9f030402 ; undefined
 2d0:	03040200 	.inst	0x03040200 ; undefined
 2d4:	00113a02 	.inst	0x00113a02 ; undefined
 2d8:	06010402 	.inst	0x06010402 ; undefined
 2dc:	83870666 	.inst	0x83870666 ; undefined
 2e0:	03040200 	.inst	0x03040200 ; undefined
 2e4:	0402004b 	.inst	0x0402004b ; undefined
 2e8:	11240203 	add	w3, w16, #0x900
 2ec:	01040200 	.inst	0x01040200 ; undefined
 2f0:	84066606 	.inst	0x84066606 ; undefined
 2f4:	0200b92f 	.inst	0x0200b92f ; undefined
 2f8:	82060104 	.inst	0x82060104 ; undefined
 2fc:	00240806 	.inst	0x00240806 ; NYI
 300:	4b030402 	sub	w2, w0, w3, lsl #1
 304:	03040200 	.inst	0x03040200 ; undefined
 308:	0402009d 	.inst	0x0402009d ; undefined
 30c:	06660601 	.inst	0x06660601 ; undefined
 310:	02004ba0 	.inst	0x02004ba0 ; undefined
 314:	004b0304 	.inst	0x004b0304 ; undefined
 318:	9d030402 	.inst	0x9d030402 ; undefined
 31c:	01040200 	.inst	0x01040200 ; undefined
 320:	a0066606 	.inst	0xa0066606 ; undefined
 324:	0402004b 	.inst	0x0402004b ; undefined
 328:	02004b03 	.inst	0x02004b03 ; undefined
 32c:	009d0304 	.inst	0x009d0304 ; undefined
 330:	06010402 	.inst	0x06010402 ; undefined
 334:	4b840666 	sub	w6, w19, w4, asr #1
 338:	03040200 	.inst	0x03040200 ; undefined
 33c:	0402004b 	.inst	0x0402004b ; undefined
 340:	02009d03 	.inst	0x02009d03 ; undefined
 344:	66060104 	.inst	0x66060104 ; undefined
 348:	2f4c8406 	.inst	0x2f4c8406 ; undefined
 34c:	01000402 	.inst	0x01000402 ; undefined
 350:	Address 0x0000000000000350 is out of bounds.


Disassembly of section .debug_str:

0000000000000000 <.debug_str>:
   0:	6e676942 	.inst	0x6e676942 ; undefined
   4:	62006d75 	.inst	0x62006d75 ; undefined
   8:	73657479 	.inst	0x73657479 ; undefined
   c:	6f72665f 	sqshlu	v31.2d, v18.2d, #50
  10:	69625f6d 	ldpsw	x13, x23, [x27,#-240]
  14:	6d756e67 	ldp	d7, d27, [x19,#-176]
  18:	736e7500 	.inst	0x736e7500 ; undefined
  1c:	656e6769 	.inst	0x656e6769 ; undefined
  20:	6e692064 	usubl2	v4.4s, v3.8h, v9.8h
  24:	6c6d0074 	ldnp	d20, d0, [x3,#-304]
  28:	47006e65 	.inst	0x47006e65 ; undefined
  2c:	4320554e 	.inst	0x4320554e ; undefined
  30:	392e3420 	strb	w0, [x1,#2957]
  34:	3220312e 	orr	w14, w9, #0x1fff
  38:	30343130 	adr	x16, 6865d <secure_bios_bignum_code+0x685cd>
  3c:	20393235 	.inst	0x20393235 ; undefined
  40:	65727028 	.inst	0x65727028 ; undefined
  44:	656c6572 	.inst	0x656c6572 ; undefined
  48:	29657361 	ldp	w1, w28, [x27,#-216]
  4c:	676d2d20 	.inst	0x676d2d20 ; undefined
  50:	72656e65 	.inst	0x72656e65 ; undefined
  54:	722d6c61 	ands	w1, w3, #0xfff87fff
  58:	2d736765 	ldp	s5, s25, [x27,#-104]
  5c:	796c6e6f 	ldrh	w15, [x19,#5686]
  60:	6c6d2d20 	ldnp	d0, d11, [x9,#-304]
  64:	6c747469 	ldnp	d9, d29, [x3,#-192]
  68:	6e652d65 	uqsub	v5.8h, v11.8h, v5.8h
  6c:	6e616964 	fcvtxn2	v4.4s, v11.2d
  70:	616d2d20 	.inst	0x616d2d20 ; undefined
  74:	6c3d6962 	stnp	d2, d26, [x11,#-48]
  78:	20343670 	.inst	0x20343670 ; undefined
  7c:	2d20672d 	stp	s13, s25, [x25,#-256]
  80:	65726666 	.inst	0x65726666 ; undefined
  84:	61747365 	.inst	0x61747365 ; undefined
  88:	6e69646e 	umax	v14.8h, v3.8h, v9.8h
  8c:	662d2067 	.inst	0x662d2067 ; undefined
  90:	636e7566 	.inst	0x636e7566 ; undefined
  94:	6e6f6974 	.inst	0x6e6f6974 ; undefined
  98:	6365732d 	.inst	0x6365732d ; undefined
  9c:	6e6f6974 	.inst	0x6e6f6974 ; undefined
  a0:	662d2073 	.inst	0x662d2073 ; undefined
  a4:	61746164 	.inst	0x61746164 ; undefined
  a8:	6365732d 	.inst	0x6365732d ; undefined
  ac:	6e6f6974 	.inst	0x6e6f6974 ; undefined
  b0:	662d2073 	.inst	0x662d2073 ; undefined
  b4:	732d6f6e 	.inst	0x732d6f6e ; undefined
  b8:	6b636174 	.inst	0x6b636174 ; undefined
  bc:	6f72702d 	.inst	0x6f72702d ; undefined
  c0:	74636574 	.inst	0x74636574 ; undefined
  c4:	6600726f 	.inst	0x6600726f ; undefined
  c8:	62656572 	.inst	0x62656572 ; undefined
  cc:	6461006e 	.inst	0x6461006e ; undefined
  d0:	646e6564 	.inst	0x646e6564 ; undefined
  d4:	646f6d00 	.inst	0x646f6d00 ; undefined
  d8:	00776f70 	.inst	0x00776f70 ; undefined
  dc:	64726f77 	.inst	0x64726f77 ; undefined
  e0:	74616400 	.inst	0x74616400 ; undefined
  e4:	6e690061 	uaddl2	v1.4s, v3.8h, v9.8h
  e8:	6e726574 	umax	v20.8h, v11.8h, v18.8h
  ec:	6d5f6c61 	ldp	d1, d27, [x3,#496]
  f0:	7500646f 	.inst	0x7500646f ; undefined
  f4:	6769736e 	.inst	0x6769736e ; undefined
  f8:	2064656e 	.inst	0x2064656e ; undefined
  fc:	72616863 	.inst	0x72616863 ; undefined
 100:	67696200 	.inst	0x67696200 ; undefined
 104:	2e6d756e 	uabd	v14.4h, v11.4h, v13.4h
 108:	73620063 	.inst	0x73620063 ; undefined
 10c:	74666968 	.inst	0x74666968 ; undefined
 110:	6e6f6c00 	umin	v0.8h, v0.8h, v15.8h
 114:	6e752067 	usubl2	v7.4s, v3.8h, v21.8h
 118:	6e676973 	.inst	0x6e676973 ; undefined
 11c:	69206465 	.inst	0x69206465 ; undefined
 120:	7400746e 	.inst	0x7400746e ; undefined
 124:	00706d65 	.inst	0x00706d65 ; undefined
 128:	726f6873 	.inst	0x726f6873 ; undefined
 12c:	6e752074 	usubl2	v20.4s, v3.8h, v21.8h
 130:	6e676973 	.inst	0x6e676973 ; undefined
 134:	69206465 	.inst	0x69206465 ; undefined
 138:	7300746e 	.inst	0x7300746e ; undefined
 13c:	72756365 	.inst	0x72756365 ; undefined
 140:	69625f65 	ldpsw	x5, x23, [x27,#-240]
 144:	625f736f 	.inst	0x625f736f ; undefined
 148:	756e6769 	.inst	0x756e6769 ; undefined
 14c:	65685f6d 	.inst	0x65685f6d ; undefined
 150:	72656461 	.inst	0x72656461 ; undefined
 154:	68736d00 	.inst	0x68736d00 ; undefined
 158:	00746669 	.inst	0x00746669 ; undefined
 15c:	75636573 	.inst	0x75636573 ; undefined
 160:	625f6572 	.inst	0x625f6572 ; undefined
 164:	5f736f69 	.inst	0x5f736f69 ; undefined
 168:	6e676962 	.inst	0x6e676962 ; undefined
 16c:	635f6d75 	.inst	0x635f6d75 ; undefined
 170:	0065646f 	.inst	0x0065646f ; undefined
 174:	65746e69 	.inst	0x65746e69 ; undefined
 178:	6c616e72 	ldnp	d18, d27, [x19,#-496]
 17c:	6c756d5f 	ldnp	d31, d27, [x10,#-176]
 180:	79626e00 	ldrh	w0, [x16,#4406]
 184:	00736574 	.inst	0x00736574 ; undefined
 188:	65736162 	.inst	0x65736162 ; undefined
 18c:	706f2f00 	adr	x0, de76f <secure_bios_bignum_code+0xde6df>
 190:	72742f74 	.inst	0x72742f74 ; undefined
 194:	65747375 	.inst	0x65747375 ; undefined
 198:	72615f64 	.inst	0x72615f64 ; undefined
 19c:	61702f6d 	.inst	0x61702f6d ; undefined
 1a0:	67616b63 	.inst	0x67616b63 ; undefined
 1a4:	732f7365 	.inst	0x732f7365 ; undefined
 1a8:	72756365 	.inst	0x72756365 ; undefined
 1ac:	69625f65 	ldpsw	x5, x23, [x27,#-240]
 1b0:	732f736f 	.inst	0x732f736f ; undefined
 1b4:	72756365 	.inst	0x72756365 ; undefined
 1b8:	69625f65 	ldpsw	x5, x23, [x27,#-240]
 1bc:	702f736f 	adr	x15, 5f02b <secure_bios_bignum_code+0x5ef9b>
 1c0:	6c00696b 	stnp	d11, d26, [x11]
 1c4:	20676e6f 	.inst	0x20676e6f ; undefined
 1c8:	676e6f6c 	.inst	0x676e6f6c ; undefined
 1cc:	736e7520 	.inst	0x736e7520 ; undefined
 1d0:	656e6769 	.inst	0x656e6769 ; undefined
 1d4:	6e692064 	usubl2	v4.4s, v3.8h, v9.8h
 1d8:	6c610074 	ldnp	d20, d0, [x3,#-496]
 1dc:	6e006e65 	.inst	0x6e006e65 ; undefined
 1e0:	65626d75 	.inst	0x65626d75 ; undefined
 1e4:	73710072 	.inst	0x73710072 ; undefined
 1e8:	74666968 	.inst	0x74666968 ; undefined
 1ec:	7a697300 	.inst	0x7a697300 ; undefined
 1f0:	70797465 	adr	x5, f307f <secure_bios_bignum_code+0xf2fef>
 1f4:	6f6c0065 	mla	v5.8h, v3.8h, v12.h[2]
 1f8:	6c20676e 	stnp	d14, d25, [x27,#-512]
 1fc:	20676e6f 	.inst	0x20676e6f ; undefined
 200:	00746e69 	.inst	0x00746e69 ; undefined
 204:	72616863 	.inst	0x72616863 ; undefined
 208:	746e6900 	.inst	0x746e6900 ; undefined
 20c:	616e7265 	.inst	0x616e7265 ; undefined
 210:	64615f6c 	.inst	0x64615f6c ; undefined
 214:	68735f64 	.inst	0x68735f64 ; undefined
 218:	65746669 	.inst	0x65746669 ; undefined
 21c:	79620064 	ldrh	w4, [x3,#4352]
 220:	73006574 	.inst	0x73006574 ; undefined
 224:	74666968 	.inst	0x74666968 ; undefined
 228:	67696200 	.inst	0x67696200 ; undefined
 22c:	5f6d756e 	sqshl	d14, d11, #45
 230:	6d6f7266 	ldp	d6, d28, [x19,#-272]
 234:	7479625f 	.inst	0x7479625f ; undefined
 238:	62007365 	.inst	0x62007365 ; undefined
 23c:	656c5f6e 	.inst	0x656c5f6e ; undefined
 240:	6572006e 	.inst	0x6572006e ; undefined
 244:	746c7573 	.inst	0x746c7573 ; undefined
 248:	6f757100 	.inst	0x6f757100 ; undefined
 24c:	656c0074 	.inst	0x656c0074 ; undefined
 250:	6874676e 	.inst	0x6874676e ; undefined
 254:	77656e00 	.inst	0x77656e00 ; undefined
 258:	Address 0x0000000000000258 is out of bounds.


Disassembly of section .comment:

0000000000000000 <.comment>:
   0:	43434700 	.inst	0x43434700 ; undefined
   4:	6328203a 	.inst	0x6328203a ; undefined
   8:	73736f72 	.inst	0x73736f72 ; undefined
   c:	6c6f6f74 	ldnp	d20, d27, [x27,#-272]
  10:	20474e2d 	.inst	0x20474e2d ; undefined
  14:	616e696c 	.inst	0x616e696c ; undefined
  18:	312d6f72 	adds	w18, w27, #0xb5b
  1c:	2e33312e 	usubw	v14.8h, v9.8h, v19.8b
  20:	2e342d31 	uqsub	v17.8b, v9.8b, v20.8b
  24:	30322d39 	adr	x25, 645c9 <secure_bios_bignum_code+0x64539>
  28:	302e3431 	adr	x17, 5c6ad <secure_bios_bignum_code+0x5c61d>
  2c:	202d2037 	.inst	0x202d2037 ; undefined
  30:	616e694c 	.inst	0x616e694c ; undefined
  34:	47206f72 	.inst	0x47206f72 ; undefined
  38:	34204343 	cbz	w3, 408a0 <secure_bios_bignum_code+0x40810>
  3c:	322d392e 	orr	w14, w9, #0xfff80003
  40:	2e343130 	usubw	v16.8h, v9.8h, v20.8b
  44:	20293630 	.inst	0x20293630 ; undefined
  48:	2e392e34 	uqsub	v20.8b, v17.8b, v25.8b
  4c:	30322031 	adr	x17, 64451 <secure_bios_bignum_code+0x643c1>
  50:	35303431 	cbnz	w17, 606d4 <secure_bios_bignum_code+0x60644>
  54:	28203932 	stnp	w18, w14, [x9,#-256]
  58:	72657270 	.inst	0x72657270 ; undefined
  5c:	61656c65 	.inst	0x61656c65 ; undefined
  60:	00296573 	.inst	0x00296573 ; NYI

Disassembly of section .debug_frame:

0000000000000000 <.debug_frame>:
   0:	0000000c 	.inst	0x0000000c ; undefined
   4:	ffffffff 	.inst	0xffffffff ; undefined
   8:	7c020001 	stur	h1, [x0,#32]
   c:	001f0c1e 	.inst	0x001f0c1e ; undefined
  10:	0000001c 	.word	0x0000001c
	...
  20:	0000017c 	.word	0x0000017c
  24:	00000000 	.word	0x00000000
  28:	02400e42 	.word	0x02400e42
  2c:	00000eba 	.word	0x00000eba
  30:	0000001c 	.word	0x0000001c
	...
  40:	000000cc 	.word	0x000000cc
  44:	00000000 	.word	0x00000000
  48:	02300e42 	.word	0x02300e42
  4c:	00000e62 	.word	0x00000e62
  50:	0000002c 	.word	0x0000002c
	...
  60:	000003e8 	.word	0x000003e8
  64:	00000000 	.word	0x00000000
  68:	9d700e42 	.word	0x9d700e42
  6c:	421a9e1c 	.word	0x421a9e1c
  70:	ee031d0d 	.word	0xee031d0d
  74:	0cddde01 	.word	0x0cddde01
  78:	0000001f 	.word	0x0000001f
  7c:	00000000 	.word	0x00000000
  80:	00000024 	.word	0x00000024
	...
  90:	00000078 	.word	0x00000078
  94:	00000000 	.word	0x00000000
  98:	9d300e42 	.word	0x9d300e42
  9c:	420a9e0c 	.word	0x420a9e0c
  a0:	de761d0d 	.word	0xde761d0d
  a4:	001f0cdd 	.word	0x001f0cdd
  a8:	00000024 	.word	0x00000024
	...
  b8:	00000040 	.word	0x00000040
  bc:	00000000 	.word	0x00000000
  c0:	9d200e42 	.word	0x9d200e42
  c4:	42069e08 	.word	0x42069e08
  c8:	de5a1d0d 	.word	0xde5a1d0d
  cc:	001f0cdd 	.word	0x001f0cdd
  d0:	0000002c 	.word	0x0000002c
	...
  e0:	000001c0 	.word	0x000001c0
  e4:	00000000 	.word	0x00000000
  e8:	9d400e42 	.word	0x9d400e42
  ec:	420e9e10 	.word	0x420e9e10
  f0:	da021d0d 	.word	0xda021d0d
  f4:	1f0cddde 	.word	0x1f0cddde
	...
 100:	0000002c 	.word	0x0000002c
	...
 110:	00000190 	.word	0x00000190
 114:	00000000 	.word	0x00000000
 118:	9d300e42 	.word	0x9d300e42
 11c:	420a9e0c 	.word	0x420a9e0c
 120:	c2021d0d 	.word	0xc2021d0d
 124:	1f0cddde 	.word	0x1f0cddde
	...
 130:	0000002c 	.word	0x0000002c
	...
 140:	00000894 	.word	0x00000894
 144:	00000000 	.word	0x00000000
 148:	01800e42 	.word	0x01800e42
 14c:	1e9e209d 	.word	0x1e9e209d
 150:	031d0d42 	.word	0x031d0d42
 154:	ddde0444 	.word	0xddde0444
 158:	00001f0c 	.word	0x00001f0c
 15c:	00000000 	.word	0x00000000
