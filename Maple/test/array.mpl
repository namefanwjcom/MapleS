entryfunc &main
func &main public () i32
func &main public () i32 {

  var %retvar_2 i32
  var %a <[3] i32>

  #int a[3] = {0, 1, 2};
  #return a[0];
  iassign <* i32> 0 (
    array 0 ptr <* <[3] i32>> (addrof ptr %a, constval i32 0), 
    constval i32 0)
  iassign <* i32> 0 (
    array 0 ptr <* <[3] i32>> (addrof ptr %a, constval i32 1), 
    constval i32 1)
  iassign <* i32> 0 (
    array 0 ptr <* <[3] i32>> (addrof ptr %a, constval i32 2), 
    constval i32 2)
  #eval (iread i32 <* i32> 0 (array 0 ptr <* <[3] i32>> (addrof ptr %a, constval i32 0)))
  #return (constval i32 0)
  return (iread i32 <* i32> 0 (array 0 ptr <* <[3] i32>> (addrof ptr %a, constval i32 0)))
}
