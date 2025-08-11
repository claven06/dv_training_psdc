class fa_tran extends uvm_sequence_item;
  rand bit a;
  rand bit b;
  rand bit cin;
  bit sum;
  bit cout;
  int seq_count;
  int seq_index;
  int tran_count;
  int tran_index;
  string seq_type;
  string tran_type;

  `uvm_object_utils(fa_tran)

  function new(string name = "fa_tran");
    super.new(name);
  endfunction
endclass
