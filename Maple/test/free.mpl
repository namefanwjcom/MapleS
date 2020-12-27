entryfunc &main
func &main public () i32
func &main public () i32 {

  var %retvar_2 i32
  var %p <* i32>
  var %retvar_3 <* void>
  var %i i32
  var %condvar_6 i32
  var %post_7 i32

  #int* p = (int*)malloc(3*sizeof(int));
  dassign %retvar_3 0 (malloc ptr (mul u64 (
    cvt u64 i32 (constval i32 3),
    sizeoftype u64 i32)))
  dassign %p 0 (dread ptr %retvar_3)
  #for (int i = 0; i <3; i++) {
  #int i = 0; i <3; i++) {
  dassign %i 0 (constval i32 0)
  dassign %condvar_6 0 (lt i32 i32 (dread i32 %i, constval i32 3))
  while (dread i32 %condvar_6) {
    #p[i] = (i + 1) * 100;
    iassign <* i32> 0 (
      array 0 ptr <* <[0] i32>> (dread ptr %p, dread i32 %i), 
      mul i32 (
        add i32 (dread i32 %i, constval i32 1),
        constval i32 100))
    dassign %post_7 0 (dread i32 %i)
    dassign %i 0 (add i32 (dread i32 %i, constval i32 1))
    dassign %condvar_6 0 (lt i32 i32 (dread i32 %i, constval i32 3))
  }
  eval (add i32 (
    add i32 (
      iread i32 <* i32> 0 (array 0 ptr <* <[0] i32>> (dread ptr %p, constval i32 0)),
      iread i32 <* i32> 0 (array 0 ptr <* <[0] i32>> (dread ptr %p, constval i32 1))),
    iread i32 <* i32> 0 (array 0 ptr <* <[0] i32>> (dread ptr %p, constval i32 2))))
  #free(dread ptr %p)
  #return p[0] + p[1] + p[2];
  return (iread i32 <* i32> 0 (array 0 ptr <* <[0] i32>> (dread ptr %p, constval i32 0)))
}

