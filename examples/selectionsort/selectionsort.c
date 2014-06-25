#include <stdio.h>
#include <stdlib.h>
#include "../../boolector.h"
#include "../../btorutil.h"

int
main (int argc, char **argv)
{
  int num_bits, num_bits_index, num_elements, i, j;
  Btor *btor;
  BtorNode **indices, *array, *min_index, *min_element, *cur_element;
  BtorNode *old_element, *index, *ne, *ult, *ulte, *temp, *read1, *read2;
  BtorNode *no_diff_element, *sorted, *formula;
  if (argc != 3)
  {
    printf ("Usage: ./selectionsort <num-bits> <num-elements>\n");
    return 1;
  }
  num_bits = atoi (argv[1]);
  if (num_bits <= 0)
  {
    printf ("Number of bits must be greater than zero\n");
    return 1;
  }
  num_elements = atoi (argv[2]);
  if (num_elements <= 1)
  {
    printf ("Number of elements must be greater than one\n");
    return 1;
  }
  if (!btor_is_power_of_2_util (num_elements))
  {
    printf ("Number of elements must be a power of two\n");
    return 1;
  }
  num_bits_index = btor_log_2_util (num_elements);
  btor           = boolector_new ();
  boolector_set_opt_rewrite_level (btor, 0);
  indices = (BtorNode **) malloc (sizeof (BtorNode *) * num_elements);
  for (i = 0; i < num_elements; i++)
    indices[i] = boolector_int (btor, i, num_bits_index);
  array = boolector_array (btor, num_bits, num_bits_index, "array");
  /* read at an arbitrary index (needed later): */
  index       = boolector_var (btor, num_bits_index, "index");
  old_element = boolector_read (btor, array, index);
  /* selection sort algorithm */
  for (i = 0; i < num_elements - 1; i++)
  {
    min_element = boolector_read (btor, array, indices[i]);
    min_index   = boolector_copy (btor, indices[i]);
    for (j = i + 1; j < num_elements; j++)
    {
      cur_element = boolector_read (btor, array, indices[j]);
      ult         = boolector_ult (btor, cur_element, min_element);
      /* found new minimum ? */
      temp = boolector_cond (btor, ult, cur_element, min_element);
      boolector_release (btor, min_element);
      min_element = temp;
      /* new minimium index ? */
      temp = boolector_cond (btor, ult, indices[j], min_index);
      boolector_release (btor, min_index);
      min_index = temp;
      /* clean up */
      boolector_release (btor, cur_element);
      boolector_release (btor, ult);
    }
    /* swap elements */
    read1 = boolector_read (btor, array, min_index);
    read2 = boolector_read (btor, array, indices[i]);
    temp  = boolector_write (btor, array, indices[i], read1);
    boolector_release (btor, array);
    array = temp;
    temp  = boolector_write (btor, array, min_index, read2);
    boolector_release (btor, array);
    array = temp;
    /* clean up */
    boolector_release (btor, read1);
    boolector_release (btor, read2);
    boolector_release (btor, min_index);
    boolector_release (btor, min_element);
  }
  /* show that array is sorted */
  sorted = boolector_const (btor, "1");
  for (i = 0; i < num_elements - 1; i++)
  {
    read1 = boolector_read (btor, array, indices[i]);
    read2 = boolector_read (btor, array, indices[i + 1]);
    ulte  = boolector_ulte (btor, read1, read2);
    temp  = boolector_and (btor, sorted, ulte);
    boolector_release (btor, sorted);
    sorted = temp;
    boolector_release (btor, read1);
    boolector_release (btor, read2);
    boolector_release (btor, ulte);
  }
  /* It is not the case that there exists an element in
   * the initial array which does not occur in the sorted
   * array.*/
  no_diff_element = boolector_const (btor, "1");
  for (i = 0; i < num_elements; i++)
  {
    read1 = boolector_read (btor, array, indices[i]);
    ne    = boolector_ne (btor, read1, old_element);
    temp  = boolector_and (btor, no_diff_element, ne);
    boolector_release (btor, no_diff_element);
    no_diff_element = temp;
    boolector_release (btor, read1);
    boolector_release (btor, ne);
  }
  temp = boolector_not (btor, no_diff_element);
  boolector_release (btor, no_diff_element);
  no_diff_element = temp;
  /* we conjunct this with the sorted predicate */
  formula = boolector_and (btor, sorted, no_diff_element);
  /* we negate the formula and show that it is unsatisfiable */
  temp = boolector_not (btor, formula);
  boolector_release (btor, formula);
  formula = temp;
  boolector_dump_btor (btor, stdout, formula);
  /* clean up */
  for (i = 0; i < num_elements; i++) boolector_release (btor, indices[i]);
  boolector_release (btor, old_element);
  boolector_release (btor, index);
  boolector_release (btor, formula);
  boolector_release (btor, no_diff_element);
  boolector_release (btor, sorted);
  boolector_release (btor, array);
  boolector_delete (btor);
  free (indices);
  return 0;
}
