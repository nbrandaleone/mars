#module RubyLabs

=begin rdoc
  
== MarsLab

The MARSLab module has definitions of classes and methods used in the projects for Chapter 8
of <em>Explorations in Computing</em>.  

The module has a Ruby implementation of the MARS 
virtual machine used in the game of Core War.
The machine implemented here conforms as close as possible to the ICWS'88 standard,
as described by Mark Durham in his Introduction to Redcode (http://corewar.co.uk/guides.htm).  

Instructions and data in a MARS program are represented by Word objects.  
Each Word has an opcode and two operands (A and B).  Integer data is represented by a Word where the opcode
field is DAT.  Other Word objects have names of executable machine instructions for opcodes.

To test a single program users can make an instance of a class named MiniMARS, passing
it the name of a test program.  The test machine will have a small memory, only big enough
to hold the test machine, and special versions of the step, dump and other methods.

The main machine that runs one, two, or three programs simultaneously is in the module
named MARS.  Methods that assemble, load, and run programs are module methods, e.g.
to assemble a program call MARS.assemble(foo).
#--
TODO add [] and []= methods to Word, use it to extract/assign bits or ranges of bits
TODO define ranges for fields, e.g. @@opcode = 0..3; use to get opcode of Word, e.g. instr[@@opcode]
TODO make sure all code uses [] interface (e.g. no more instr.amode[0] == ?#)
TODO pack words into binary -- will kill several birds at once -- speed, trim values to 0..4095, ..
TODO color a cell black when a thread halts after executing an instruction in that cell
TODO MARS.dump
TODO pass load address to contest (which passes it on to Warrior.load)?
#++
=end
  
module MARSLab
  
    # -- Initializations -- These are "global" vars in the outer MARSLab scope that are
    # accessible to all the classes and modules defined inside MARSLab
  
  @@marsDirectory = File.join(File.dirname(__FILE__), '..', 'data', 'mars')

  @@opcodes = ["DAT", "MOV", "ADD", "SUB", "JMP", "JMZ", "JMN", "DJN", "CMP", "SPL", "END", "SLT", "EQU"]
  @@modes = "@<#"

  @@maxEntries = 3
  @@displayMemSize = 4096

  @@params = {
    :maxRounds => 1000,
    :memSize => @@displayMemSize,
    :buffer => 100,
    :tracing => false,
    :pause => 0.01,
  }
  
  MARSView = Struct.new(:cells, :palettes, :options)

  @@viewOptions = {
    :cellSize => 8,
    :cellRows => 32,
    :cellCols => 128,
    :padding => 20,
    :traceSize => 10,
    :cellColor => '#DDDDDD',
  }

  @@drawing = nil
  
=begin rdoc
  A MARSRuntimeException is raised when MARS tries to execute an illegal instruction,
  e.g. when a program contains an instruction with the wrong type of addressing mode for
  its opcode.
=end

  class MARSRuntimeException < StandardError
  end
  
=begin rdoc
  A RedcodeSyntaxError is raised when a source program contains an instruction that cannot
  be translated into MARS machine language, e.g. it has an unknown opcode or a missing operand.
=end

  class RedcodeSyntaxError < StandardError
  end

=begin rdoc

== Word

An object of the Word class represents a single item from memory, either a machine 
instruction or a piece of data.  Attributes are the opcode, the A operand mode, and 
the B operand (all strings).  Instruction execution proceeds according to the description 
in Durham's spec.

=end

  class Word
    
    attr_reader :op, :lineno
    attr_accessor :a, :b
    
    # Create a new Word from +op+, +a+, +b+, and +n+.
    # :call-seq:
    #   Word.new(op, a, b, n) => Word
    #
        
    def initialize(*args)
      @op, @a, @b, @lineno = args
    end
    
    # Return a string representation of this word.
    
    def inspect
      sprintf "%s %s %s", @op, @a, @b
    end
    
    alias to_s inspect
    
    # Two Words are the same if the strings representing the opcode and
    # both operands are the same.
    
    def ==(other)
      return (op == other.op && a == other.a && b == other.b)
    end
    
    # Make a new Word object with all the same attributes as this object.
    
    def clone
      Word.new(@op.clone, @a.clone, @b.clone, @lineno)
    end
    
    # Convert a field specification into an integer value, stripping off a leading
    # addressing mode character if it's there
    
    def field_value(field)
      return @@modes.include?(field[0]) ? field[1..-1].to_i : field.to_i
    end
    
    # Return the address of an operand; note that for immediate operands the 
    # address is the address of the current instruction.
    
    def dereference(field, pc, mem)
      case field[0]
      when ?#
        return pc.current[:addr]
      when ?@
        ptrloc = (field_value(field) + pc.current[:addr]) % mem.size
        ptr = mem.fetch(ptrloc)
        return (field_value(ptr.b) + ptrloc) % mem.size
      when ?<
        ptrloc = (field_value(field) + pc.current[:addr]) % mem.size
        ptr = mem.fetch(ptrloc)
        newb = field_value(ptr.b) - 1
        mem.store_field(ptrloc, (newb % mem.size), :b)
        return (newb + ptrloc) % mem.size
      else
        return (field_value(field) + pc.current[:addr]) % mem.size
      end
    end
    
    # Execute the instruction represented by this word.  The first parameter is the program counter used
    # to fetch the instruction, the second is the machine's memory array.  
    #
    # The semantics for each type of instruction are defined by private methods that have the same
    # name as the opcode, e.g. then the opcode is "ADD" execute calls +ADD+, sending it the +pc+ and
    # +mem+ arguments so the instruction can dereference its arguments and carry out the specified operation.
    
    def execute(pc, mem)
      self.send(@op, pc, mem)
      return (@op == "DAT") ? (:halt) : (:continue) 
    end
    
    private
    
    # The DAT instruction is effectively a "halt", but we still need to dereference
    # both its operands to generate the side effects in auto-decrement modes.
    
    def DAT(pc, mem)    # :doc:
      dereference(@a, pc, mem)
      dereference(@b, pc, mem)
    end
    
    # Durham isn't clear on how to handle immediate moves -- does the immediate value
    # go in the A or B field of the destination?  Guess:  B, in case the destination
    # is a DAT.
        
    def MOV(pc, mem)    # :doc:
      raise MARSRuntimeException, "MOV: immediate B-field not allowed" if @b[0] == ?#
      src = dereference(@a, pc, mem)
      val = mem.fetch(src)
      dest = dereference(@b, pc, mem)
      if @a[0] == ?#
        mem.store_field(dest, field_value(val.a), :b)
      else
        mem.store(dest, val)
      end
      pc.log(src)
      pc.log(dest)
    end
    
    # Ambiguity on how to handle immediate A values:  add operand to the A or B
    # field of the destination?  Guess:  B (for same reasons given for MOV)

    def ADD(pc, mem)    # :doc:
      raise MARSRuntimeException, "ADD: immediate B-field not allowed" if @b[0] == ?#
      src = dereference(@a, pc, mem)
      left_operand = mem.fetch(src)
      dest = dereference(@b, pc, mem)
      right_operand = mem.fetch(dest)
      if @a[0] == ?#
        mem.store_field(dest, field_value(left_operand.a) + field_value(right_operand.b), :b)
      else
        mem.store_field(dest, field_value(left_operand.a) + field_value(right_operand.a), :a)
        mem.store_field(dest, field_value(left_operand.b) + field_value(right_operand.b), :b)
      end
      pc.log(src)
      pc.log(dest)
    end
    
    # See note for ADD, re immediate A operand.
    
    def SUB(pc, mem)    # :doc:
      raise MARSRuntimeException, "SUB: immediate B-field not allowed" if @b[0] == ?#
      src = dereference(@a, pc, mem)
      right_operand = mem.fetch(src)
      dest = dereference(@b, pc, mem)
      left_operand = mem.fetch(dest)
      if @a[0] == ?#
        mem.store_field(dest, field_value(left_operand.b) - field_value(right_operand.a), :b)
      else
        mem.store_field(dest, field_value(left_operand.a) - field_value(right_operand.a), :a)
        mem.store_field(dest, field_value(left_operand.b) - field_value(right_operand.b), :b)
      end
      pc.log(src)
      pc.log(dest)
    end
    
    # Durham doesn't mention this explicitly, but since a B operand is allowed it implies
    # we have to dereference it in case it has a side effect.
        
    def JMP(pc, mem)    # :doc:
      raise MARSRuntimeException, "JMP: immediate A-field not allowed" if @a[0] == ?#
      target = dereference(@a, pc, mem) % mem.size
      dereference(@b, pc, mem)
      pc.branch(target)
    end
    
    # Branch to address specified by A if the B-field of the B operand is zero.
    
    def JMZ(pc, mem)    # :doc:
      raise MARSRuntimeException, "JMZ: immediate A-field not allowed" if @a[0] == ?#
      target = dereference(@a, pc, mem) % mem.size
      operand = mem.fetch(dereference(@b, pc, mem))
      if field_value(operand.b) == 0
        pc.branch(target)
      end
    end
    
    # As in JMZ, but branch if operand is non-zero
    
    def JMN(pc, mem)    # :doc:
      raise MARSRuntimeException, "JMN: immediate A-field not allowed" if @a[0] == ?#
      target = dereference(@a, pc, mem) % mem.size
      operand = mem.fetch(dereference(@b, pc, mem))
      if field_value(operand.b) != 0
        pc.branch(target)
      end
    end
    
    # DJN combines the auto-decrement mode dereference logic with a branch -- take
    # the branch if the new value of the B field of the pointer is non-zero.
    
    def DJN(pc, mem)    # :doc:
      raise MARSRuntimeException, "DJN: immediate A-field not allowed" if @a[0] == ?#
      target = dereference(@a, pc, mem)
      operand_addr = dereference(@b, pc, mem)
      operand = mem.fetch(operand_addr)
      newb = field_value(operand.b) - 1
      mem.store_field(operand_addr, (newb % mem.size), :b)
      if newb != 0
        pc.branch(target)
      end
      pc.log(operand_addr)
    end
    
    # Durham just says "compare two fields" if the operand is immediate.  Since
    # B can't be immediate, we just need to look at the A operand and, presumably,
    # compare it to the A operand of the dereferenced operand fetched by the B field.
    # If A is not immediate compare two full Words -- including op codes.  
    # The call to pc.next increments the program counter for this thread, which causes 
    # the skip.

    def CMP(pc, mem)    # :doc:
      raise MARSRuntimeException, "CMP: immediate B-field not allowed" if @b[0] == ?#
      right = mem.fetch(dereference(@b, pc, mem))
      if @a[0] == ?#
        left = field_value(@a)
        right = field_value(right.a)
      else
        left = mem.fetch(dereference(@a, pc, mem))
      end
      if left == right
        pc.next
      end
    end
    
    # More ambiguity here -- what does it mean for a word A to be "less than"
    # word B?  First assumption, don't compare opcodes.  Second, we're just going
    # to implement one-field comparisons of B fields.  Otherwise for full-word operands
    # we'd need to do a lexicographic compare of A and B fields of both operands, skipping
    # modes and just comparing values.
    
    def SLT(pc, mem)    # :doc:
      raise MARSRuntimeException, "SLT: immediate B-field not allowed" if @b[0] == ?#
      if @a[0] == ?#
        left = field_value(@a)
      else
        left = field_value(mem.fetch(dereference(@a, pc, mem)).b)
      end
      right = field_value(mem.fetch(dereference(@b, pc, mem)).b)
      if left < right 
        pc.next
      end
    end
    
    # Fork a new thread at the address specified by A.  The new thread goes at the end
    # of the queue.  Immediate operands are not allowed.  Durham doesn't mention it, but
    # implies only A is dereferenced, so ignore B.
    
    def SPL(pc, mem)    # :doc:
      raise MARSRuntimeException, "SPL: immediate A-field not allowed" if @a[0] == ?#
      target = dereference(@a, pc, mem)
      pc.add_thread(target)
    end
        
  end # class Word
  
  
=begin rdoc

== Warrior

A Warrior is a core warrior -- an object of this class is a simple struct that
has the program name, assembled code, the starting location, and the symbol table.

A static method (Warrior.load) will load an assembled Warrior into memory, making
sure the max number of programs is not exceeded.  The addr attribute is set to the
starting location of the program when it is loaded.
=end

  class Warrior
    attr_reader :name, :code, :symbols, :errors

    # Create a new Warrior by reading and assembling the instructions in +filename+.
    # The +code+ array is empty if there are any assembly errors.

    def initialize(filename)
      if filename.class == Symbol
        filename = File.join(@@marsDirectory, filename.to_s + ".txt")
      end

      if ! File.exist?(filename)
        raise "Can't find file: #{filename}"
      end

      @name, @code, @symbols, @errors = MARS.assemble( File.open(filename).readlines )

      if @errors.length > 0
        puts "Syntax errors in #{filename}:"
        puts errors
        @code.clear
      end
    end
    
    # Create a string with essential information about this object.

    def inspect
      sprintf "Name: #{@name} Code: #{@code.inspect}"
    end
    
    alias to_s inspect
    
    # Load the code for the Warrior object reference by +app+ into the MARS main memory.
    # If an address is specified, load that code starting at that location, otherwise
    # choose a random location.  The memory addresses used by the program are recorded
    # so programs aren't accidentally loaded on top of each other.
    
    def Warrior.load(app, addr = :random)
      if app.class != Warrior
        puts "Argument must be a Warrior object, not a #{app.class}"
        return nil
      end
     
      if @@entries.length == @@maxEntries
        puts "Maximum #{@@maxEntries} programs can be loaded at one time"
        return nil
      end
      
      if addr == :random
        loop do
          addr = rand(@@mem.size)
          break if Warrior.check_loc(addr, addr + app.code.length - 1)
        end
      else
        if ! Warrior.check_loc(addr, addr + app.code.length - 1)
          puts "Address #{addr} too close to another program; #{app.name} not loaded"
          return nil
        end
      end
      
      loc = addr
      app.code.each do |x|
        @@mem.store(loc, x)
        loc = (loc + 1) % @@mem.size
      end

      id = @@entries.length
      @@pcs << PC.new(id, addr + app.symbols[:start])
      @@entries << app
      
      # save the range of memory locations reserved by this app
      
      lb = addr - @@params[:buffer]
      ub = addr + app.code.length + @@params[:buffer] - 1
      if lb < 0
        @@in_use << ( 0 .. (addr+app.code.length-1) )
        @@in_use << ( (@@params[:memSize] + lb) .. (@@params[:memSize]-1) )
      elsif ub > @@params[:memSize]
        @@in_use << ( addr .. (@@params[:memSize]-1) )
        @@in_use << ( 0 .. (ub - @@params[:memSize]) )
      else
        @@in_use << (lb..ub)
      end
      
      return addr
    end
    
    @@in_use = Array.new
    
    # Clear the data structure that records which memory locations are in use, allowing
    # new programs to be loaded into any location.
    
    def Warrior.reset
      @@in_use = Array.new
    end
    
    private

    # Return true if a program loaded between lb and ub would not overlap another
    # program already loaded (including a buffer surrounding loaded programs).

    def Warrior.check_loc(lb, ub)   # :doc:
      @@in_use.each do |range|
        return false if range.include?(lb) || range.include?(ub)
      end
      return true
    end
    
  end # class Warrior
  
  
=begin rdoc

== PC

The PC (program counter) class is used to keep track of the next instruction to execute when a program is running.
A PC object has an array of locations to hold the next instruction from each thread, plus the
index of the thread to use on the next instruction fetch cycle.

=end

  class PC
    attr_reader :id, :thread, :addrs, :current
    
    @@hmax = 10       # see also @@threadMax in Draw -- allowed to be a different value

    # Create a new program counter.  The +id+ argument is a tag that can be used to 
    # identify which program is running at this location.  The PC is intialized with
    # one thread starting at location +addr+.
    
    def initialize(id, addr)
      @id = id
      @addrs = [addr]
      @history = [ Array.new ]
      @thread = 0
      @current = {:thread => nil, :addr => nil}
      @first = addr
    end
    
    # Restore this program counter to its original state, a single thread starting
    # at the location passed when the object was created.
    
    def reset
      @addrs = [@first]
      @history.clear
      @thread = 0
      @current = {:thread => nil, :addr => nil}
      return @first
    end
    
    # Create a string showing the name of the program and the current instruction
    # for each thread.
  
    def inspect
      s = "[ "
      @addrs.each_with_index do |x,i|
        s << "*" if i == @thread
        s << x.to_s
        s << " "
      end
      s << "]"
    end
    
    alias to_s inspect
    
    # Add a new thread, which will begin execution at location +addr+.
    #--
    # Not sure if this is right -- new thread appended to list, as per Durham, but
    # the execution stays with the current thread (thread switch happens in 'next' method)

    def add_thread(addr)
      @addrs << addr
      @history << Array.new
      self
    end
    
    # Return the address of the next instruction to execute for this program.
    # If more than one thread is active, make the next thread the current thread.
        
    def next
      return nil if @addrs.empty?
      addr = @addrs[@thread]
      @current[:thread] = @thread
      @current[:addr] = addr
      @addrs[@thread] = (@addrs[@thread] + 1) % @@mem.size
      @thread = (@thread + 1) % @addrs.size
      log(addr)
      return addr
    end
    
    # Implement a branch instruction by setting the next instruction address for the
    # current thread to +loc+.
    
    def branch(loc)
      @addrs[@current[:thread]] = loc
    end
    
    # Remove the current thread from the list of active threads.  The return value
    # is the number of remaining threads.
  
    def kill_thread
      return 0 if @addrs.empty?
      @addrs.slice!(@current[:thread])
      @history.slice!(@current[:thread])
      @thread -= 1
      return @addrs.length
    end

    # Record the location of a memory operation in the history vector for the current thread.
    # The history vector is used by the methods that display the progress of a program on
    # the RubyLabs canvas.

    def log(loc)
      a = @history[@current[:thread]]
      a << loc
      a.shift if a.length > @@hmax  
    end
    
    # Return a reference to the set of history vectors for this Warrior object.
    
    def history
      return @history
    end
    
  end # class PC
  
=begin rdoc

== Memory

An object of the Memory class is a 1-D array of the specified size.  Items in a Memory
are Word objects.

According to the Core War standard, memory should be initialized with DAT #0 instructions
before each contest.  For efficiency, newly (re)initialized Memory objects have +nil+
at each location, but +nil+ is treated the same as DAT #0.
  
=end
  
  class Memory
        
    attr_reader :array

    # Create a new Memory of the specified size.
    
    def initialize(size)
      @array = Array.new(size)
    end
    
    # Create a string describing this Memory object.
    
    def to_s
      sprintf "Memory [0..#{@array.size-1}]"
    end
        
    # Print the +n+ words in memory starting at +loc+.

    def dump(loc, n)
      (loc...(loc+n)).each do |x|
        addr = x % @array.size
        printf "%04d: %s\n", addr, self.fetch(addr) 
      end
    end

    # Return the size (number of words that can be stored) of this Memory object.
     
    def size
      return @array.size
    end
        
    # Return the Word object stored in location +loc+ in this Memory object. 
    
    def fetch(loc)
      return ( @array[loc] || Word.new("DAT", "#0", "#0", nil) )
    end
    
    # Store object +val+ in location +loc+.
    
    def store(loc, val)
      @array[loc] = val.clone
    end
    
    # Same as +fetch+, but return only the designated field of the Word stored at location +loc+.
    
    def fetch_field(loc, field)
      instr = self.fetch(loc)
      return field == :a ? instr.a : instr.b
    end
    
    # Same as +store+, but overwrite only the designated field of the Word in location +loc+.
    
    def store_field(loc, val, field)
      instr = self.fetch(loc)
      part = (field == :a) ? instr.a : instr.b
      mode = @@modes.include?(part[0]) ? part[0].chr : ""
      part.replace(mode + val.to_s)
      self.store(loc, instr)
    end
                
  end # class Memory
  
=begin rdoc

== MiniMARS

A miniature machine (MiniMARS) object is used to test a Redcode program.  It is essentially
a MARS VM connected to a "thumb drive" that contains the assembled code for a single program.
By single-stepping through the program users can learn how the code works or debug a 
program they are developing.

=end

  class MiniMARS
    attr_reader :mem, :pc, :state
    
    # Create a VM that has a memory with the assembled form of the Redcode program in +file+.
    # has been loaded into location 0.  The optional second argument defines the size
    # of the memory (otherwise the memory is just big enough to hold the program).  

    def initialize(file, size = nil)
      w = Warrior.new(file)
      @mem = size ? Memory.new(size) : Memory.new(w.code.length)
      loc = 0
      w.code.each do |x|
        @mem.store(loc, x)
        loc = loc + 1
      end
      @pc = PC.new(w.name, w.symbols[:start])
      @state = :ready
    end
   
    # Create a string with a short description of this VM.
    
    def inspect
      return "#<MiniMARS mem = #{@mem.array.inspect} pc = #{@pc}>"
    end
    
    alias to_s inspect
    
    # Print a string that describes the program status (running or halted, current
    # instruction address, ...)
    
    def status
      s = "Run: #{@state}"
      s += " PC: #{@pc}" unless @state == :halt
      puts s
    end

    # Execute the next instruction in the program loaded into this VM.  The
    # return value is the Word object for the instruction just executed.
    
    def step
      return "machine halted" if @state == :halt
      instr = @mem.fetch(@pc.next)
      @state = instr.execute(@pc, @mem)
      return instr
    end
    
    # Execute instructions in the program loaded into this VM until it hits
    # a HALT (DAT) instruction.  The return value is the number of instructions
    # executed. The optional argument is a maximum number of steps
    # to execute; afer executing this number of instructions the method will
    # return, whether or not the program halts.

    def run(nsteps = 1000)
      count = 0
      loop do
        break if @state == :halt || nsteps <= 0
        self.step
        nsteps -= 1
        count += 1
      end
      return count 
    end
    
    # Reset the program counter to 0, so the program starts over.  But the 
    # contents of memory are not restored, they are left as they were after the
    # last instruction executed.
    
    def reset
      @pc.reset
      puts "warning: memory may not be in initial state"
    end
    
    # Print the contents of the VM memory.  If two arguments are passed they
    # are used as the addresses of the first and last words to print.
    
    def dump(*args)
      if args.empty?
        @mem.dump(0, @mem.array.length)
      else
        x = args[0]
        y = args[1] || x
        @mem.dump(x, y-x+1)
      end
      return nil
    end
   
  end # MiniMARS
    
  
=begin rdoc

== MARS

The MARS class defines a singleton object that has the methods used to assemble, load, and execute
up to three Redcode programs at a time.

=end

  class MARS
  
    #  -------- Assembler ----------
  
    # line format:
    #     <label>   <opcode> <A-mode><A-field>, <B-mode><B-field>   <comment>
  
    # Parsing methods strip off and return the item they are looking for, or raise
    # an error if the line doesn't start with a well-formed item
  
    # Labels start in column 0, can be any length

    def MARS.parseLabel(s)        # :nodoc:
      return nil if s =~ /^\s/
      x = s[/^\w+/]               # set x to the label
      if x.nil?                   # x is nil if label didn't start with a word char
        raise RedcodeSyntaxError, "illegal label in '#{s}'"
      end
      if @@opcodes.include?(x.upcase)
        raise RedcodeSyntaxError, "can't use opcode '#{x}' as a label"
      end
      s.slice!(x)                 # remove it from the line
      return x                    # return it
    end
  
    # Expect opcodes to be separated from labels (or start of line) by white space
  
    def MARS.parseOpCode(s)       # :nodoc:
      if s !~ /^\s/               
        raise RedcodeSyntaxError, "illegal label in '#{s}'"
      end
      s.lstrip!
      x = s[/^\w+/]               # set x to the opcode
      if x.nil? || !@@opcodes.include?(x.upcase)
        raise RedcodeSyntaxError, "unknown opcode '#{x}'"
      end
      s.slice!(x)                 # remove it from the line
      return x.upcase             # return it
    end
  
    def MARS.parseOperand(s)      # :nodoc:
      s.lstrip!
      return s if s.length == 0
      x = s[/^[#{@@modes}]?[+-]?\w+/]
      if x.nil?
        raise RedcodeSyntaxError, "illegal operand in '#{s}'"
      end
      s.slice!(x)
      return x.upcase
    end
  
    def MARS.parseSeparator(s)    # :nodoc:
      s.lstrip!
      return if s.length == 0
      if s[0] == ?,
        s.slice!(0)
      else
        raise RedcodeSyntaxError, "operands must be separated by a comma"
      end
    end
    
    # Helper method called by the assembler to break an input line into its constituent
    # parts.  Calls its own helpers named +parseLabel+, +parseOpCode+, and +parseOperand+;
    # see marslab.rb for more information.
  
    def MARS.parse(s)
      label = MARS.parseLabel(s)
      op = MARS.parseOpCode(s)
      a = MARS.parseOperand(s)
      MARS.parseSeparator(s)
      b = MARS.parseOperand(s)
      return [label,op,a,b]
    end
  
    def MARS.saveWord(instr, label, code, symbols)    # :nodoc:    
      if instr.op == "EQU"
        operand = instr.a
        arg = operand[/[+-]?\d+/]
        operand.slice!(arg)
        raise RedcodeSyntaxError, "EQU operand must be an integer" unless operand.length == 0
        raise RedcodeSyntaxError, "EQU must have a label" if label.nil?
        symbols[label.upcase] = arg.to_i
      elsif instr.op == "END"
        if n = symbols[instr.a]
          symbols[:start] = n
        else
          raise RedcodeSyntaxError, "unknown operand in END: #{instr.a}" if instr.a.length > 0
        end
      else
        if label
          symbols[label.upcase] = code.length      # "PC" value is number of codes saved so far
        end
        code << instr
      end
    end
      
    def MARS.translate(s, symbols, loc)   # :nodoc:
      if s.length == 0
        s.insert(0, "#0")
        return true
      end
      if md = s.match(/[#{@@modes}]?(\w+)/)
        sym = md[1]
        return true if sym =~ /^[+-]?\d+$/
        return false unless symbols.has_key?(sym) 
        val = symbols[sym] - loc
        s.sub!(sym, val.to_s)
        return true
      end
      return false
    end
  
    # A simple two-pass assembler for Redcode.  The input is an array of strings read
    # from a file.  The result of the call is an array of 4 items:  
    # +name+:: the name of the program (if there was a name pseudo-op in the source code)
    # +code+:: the assembled code, in the form of an array of Word objects
    # +symbols+:: a Hash with labels and their values
    # +errors+:: an array of error messages

    def MARS.assemble(strings)
      code = Array.new              # save Word objects here
      symbols = Hash.new            # symbol table
      errors = Array.new            # put error strings here
      name = "unknown"              # default program name
      name += @@entries.size.to_s
      symbols[:start] = 0           # default starting address
    
      # Pass 1 -- create list of Word objects, build the symbol table:
    
      strings.each_with_index do |line, lineno|
        line.rstrip!
        next if line.length == 0                    # skip blank lines
        if line[0] == ?;                            # comments have ; in column 0
          if md = line.match(/;\s*name\s+(\w+)/)    # does comment have program name?
            name = md[1]                            # yes -- save it
          end
          next
        end
        if n = line.index(";")                      # if comment at end remove it
          line.slice!(n..-1)
        end
        begin
          label, op, a, b = MARS.parse(line)
          instr = Word.new(op, a, b, lineno+1)
          MARS.saveWord(instr, label, code, symbols)        
        rescue RedcodeSyntaxError
          errors << "  line #{lineno+1}: #{$!}"
        end
      end
    
      # Pass 2 -- translate labels into ints on each instruction:
      # TODO -- deal with expressions, e.g. "JMP label + 1"
    
      code.each_with_index do |instr, loc|
        if instr.op == "DAT" && instr.b.length == 0
          instr.a, instr.b = instr.b, instr.a
        end
        begin
          MARS.translate(instr.a, symbols, loc) or raise RedcodeSyntaxError, "unknown/illegal label"
          MARS.translate(instr.b, symbols, loc) or raise RedcodeSyntaxError, "unknown/illegal label"
        rescue RedcodeSyntaxError
          errors << "  line #{instr.lineno}: #{$!}"
        end
      end
    
      return [name, code, symbols, errors]
    end

    #  -------- End Assembler ----------

    # Execute one instruction from each active program.  If a thread dies remove the PC
    # from the array for that program.  A program dies when its last thread dies.  The
    # return value is the number of programs still running.
    
    def MARS.step   
      if @@entries.empty?
        puts "no programs loaded"
        return 0
      end
    
      # A list of program ids that terminate on this cycle
      done = []

      # This loop gets the current instruction from each active program and executes it.
      # The return value from the execute method is true if the thread executes a DAT
      # instruction.  The other way to stop the thread is if it has a runtime exception.
    
      @@pcs.each_with_index do |pc, id|
        loc = pc.next 
        instr = @@mem.fetch(loc)
        printf("%04d: %s\n", pc.current[:addr], instr) if @@params[:tracing]

        if @@drawing
          MARS.updateCells(pc)
          sleep(@@params[:pause])
        end
      
        begin
          signal = instr.execute(pc, @@mem)
        rescue MARSRuntimeException
          puts "runtime error: #{$!} in instruction on line #{instr.lineno}"
          signal = :halt
        end

        # If this thread halted delete the thread location from the program counter's list. 
        # The return value from kill_thread is the number of threads left -- if 0 the 
        # program is done.
      
        if signal == :halt
          if pc.kill_thread == 0
            done << id              # old C++ habit -- don't delete from container while iterating....
          end
        end
      
      end
    
      # Remove any newly terminated programs from the list of program counters, stop the machine
      # when no programs are left.

      done.each do |x|
        @@pcs.slice!(x)
      end
    
      return @@pcs.size
    
    end
  
    # Run the programs in memory, stopping when the number of surviving programs is +nleft+.  
    # To hold a contest that continues until only one program survives call <tt>Mars.run(1)</tt>,
    # but when testing a single program the call can be <tt>Mars.run(0)</tt>.  This method will
    # also return when the maximum number of instructions has been executed (determined by the runtime
    # parameter +maxRounds+).
  
    def MARS.run(nleft = 0)
      nrounds = @@params[:maxRounds]
      loop do
        nprog = MARS.step
        nrounds -= 1
        break if nprog == nleft || nrounds <= 0
      end
    end
  
    # Print information about the machine and any programs in memory.
  
    def MARS.state
      puts "MARS CPU with #{@@mem.size}-word memory"
      if @@entries.length == 0
        puts "no programs loaded"
      else
        for i in 0...@@entries.length
          puts "Program: #{@@entries[i].name}"
          puts "  code:     #{@@entries[i].code.inspect}"
          puts "  threads:  #{@@pcs[i]}"
        end
      end
      puts "Options:"
      @@params.each do |key, val|
        puts "  #{key}:  #{val}"
      end
      return true
    end
  
  
  # Set the value of one of the run-time options.  The options, and their default values, are:
  # memSize:: size of the virtual machine memory (4096 words)
  # buffer:: minimum distance between code for two warriors (100 words)
  # tracing:: when true, print detailed trace as machine runs (false)
  # pause:: amount of time to pause between screen updates when programs are run (0.01 sec)
  # maxRounds:: number of turns to give each program before calling a draw (1000)
  #
  # Example:
  #   >>!blue MARS.set_option(:pause, 0.5)
  #   => 0.5
  #
  # Note: Call MARS.state to see the current settings for the options.

    def MARS.set_option(key, val)
      if ! @@entries.empty?
        puts "Options can be set only when no programs are loaded (call 'reset' to clear programs)"
        return false
      end
      case key
      when :memSize
        if val.class != Fixnum || val < 1024 || val > 16536
          puts ":memSize must be an integer between 1024 and 16536"
          return nil
        end
      when :maxRounds, :buffer
        if val.class != Fixnum
          puts ":#{key} must be an integer"
          return nil
        end
      when :pause
        if val.class != Float
          puts ":#{key} must be an floating point number (e.g. 0.05)"
          return nil
        end
      when :tracing
        if ! (val.class == TrueClass || val.class == FalseClass)
          puts ":tracing must be true or false"
          return nil
        end
      else
        puts "Unknown option: #{key}"
        puts "Call MARS.state to see a list of options and their current settings."
        return nil
      end
      @@params[key] = val
    end
  
    # Initialize the RubyLabs canvas with a drawing of the MARS VM main memory.  The
    # display will show one rectangle for each memory cell.  When a core warrior is 
    # loaded into memory, the rectangles for the cells it occupies will change color,
    # with a different color for each contestant.  As a program runs, any memory cells
    # it references will be filled with that program's color.  To keep the screen from
    # having too much color, cells gradually fade back to gray if they are not referenced
    # for a long time.
    
    def MARS.view(userOptions = {} )

      options = @@viewOptions.merge(userOptions)
      
      cellsize = options[:cellSize]
      padding = options[:padding]
      
      width = options[:cellCols] * cellsize + 2*padding
      height = options[:cellRows] * cellsize + 2*padding
      Canvas.init(width, height, "MARSLab")
      
      cells = []
      for i in 0...@@displayMemSize
        x = (i % options[:cellCols]) * cellsize + padding
        y = (i / options[:cellCols]) * cellsize + padding
        cells << Canvas::Rectangle.new( x, y, x+cellsize, y+cellsize, :outline => "#888888", :fill => options[:cellColor] ) 
      end
      
      palettes = [
        Canvas.palette( [204,204,204], [204,100,100], options[:traceSize] ), 
        Canvas.palette( [204,204,204], [100,100,204], options[:traceSize] ),
        Canvas.palette( [204,204,204], [100,204,100], options[:traceSize] ),
      ]
      palettes[0] << "#FF0000"
      palettes[1] << "#0000FF"
      palettes[2] << "#00FF00"
      
      @@drawing = MARSView.new(cells, palettes, options)
      return true
      
    end
    
    # Close the RubyLabs Canvas window.
  
    def MARS.close_view
      Canvas.close
    end
      
    # Load up to three core warrior programs and start a contest, returning when only one
    # program is still running or when the maximum number of turns have been taken.  Arguments
    # can be symbols, in which case they are names of programs in the MARSLab data directory,
    # or strings, in which case they are interpreted as names of Redcode files in the current
    # directory. 
    # 
    # Example:
    #   >>!blue MARS.contest(:imp, :dwarf)
    #   => nil  

    def MARS.contest(*args)
      MARS.reset
      if args.length < 1 || args.length > 3
        puts "Pass one, two, or three program names"
        return nil
      end
      args.each do |x|
        Warrior.load(Warrior.new(x))
      end
      MARS.run(1)      # the 1 means stop when only 1 program left running
    end

    # Reset the machine state by clearing memory and removing all programs from
    # the list of active warriors.
    
    def MARS.reset
      @@pcs = Array.new
      @@mem = Memory.new(@@params[:memSize])
      @@entries = Array.new
      Warrior.reset
      if @@drawing
        @@drawing.cells.each do |x|
          x.fill = @@drawing.options[:cellColor]
        end
      end
      return true
    end
   
    # Print a listing of a Redcode source programs.  If the argument is a symbol, it
    # is interpreted as the name of a program in the MARSLab data directory; if it is
    # a string, it should be the name of a file in the current directory.

    def MARS.listing(prog, dest = nil)
      filename = prog.to_s
      filename += ".txt" unless filename =~ /\.txt$/
      filename = File.join(@@marsDirectory, filename)
      dest = STDOUT if dest.nil?
      if !File.exist?(filename)
        puts "File not found: #{filename}"
      else
        File.open(filename).each do |line|
          dest.puts line.chomp
        end
      end
      return nil
    end
    
    # Save a copy of a Redcode source program. 
    # A program named "x" is saved in a file named "x.txt" in the current directory
    # unless a different file name is passed as a second argument.
    # If the argument is a symbol, it
    # is interpreted as the name of a program in the MARSLab data directory; if it is
    # a string, it should be the name of a file in the current directory.

    def MARS.checkout(prog, filename = nil)
      filename = prog.to_s + ".txt" if filename.nil?
      dest = File.open(filename, "w")
      MARS.listing(prog, dest)
      dest.close
      puts "Copy of #{prog} saved in #{filename}"
    end
    
    # Print a list of programs in the MARSLab data directory.

    def MARS.dir
      puts "Redcode programs in #{@@marsDirectory}:"
      Dir.open(@@marsDirectory).each do |file|
        next if file[0] == ?.
        file.slice!(/\.txt/)
        puts "  " + file
      end
      return nil
    end
    
    private
    
    # Drawing hook, called from MARS.step when the canvas is active.
    
    def MARS.updateCells(pc)
      id = pc.id
      a = pc.history[pc.current[:thread]]
      d = @@drawing.palettes[id].length - a.length
      a.each_with_index do |x, i|
        @@drawing.cells[x].fill = @@drawing.palettes[id][i+d]
      end     
    end
      
  end # class MARS
  
  
  # Make a MiniMARS VM with a single program loaded into memory at location 0.
  # By default the size of the memory is the number of words in the program, but a memory
  # size can be passed as a second argument.
  
  def make_test_machine(file, size = nil)
    begin
      return MiniMARS.new(file, size)
    rescue Exception => e
      puts "Failed to make test machine: #{$!}"
      return nil
    end
  end
  
  @@pcs = Array.new
  @@mem = Memory.new(@@params[:memSize])
  @@entries = Array.new

end # MARSLab

#end # RubyLabs
