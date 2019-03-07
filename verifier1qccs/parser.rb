class Parser
  class NameTable
    def initialize
      @nats = Array.new
      @nats << "1"

      @channels = Hash.new
      @qvars = Hash.new
      @dsyms = Hash.new  
      @operators = Hash.new
    end

    public
    def show_all
      print " *nats:"
      p @nats
      print " *channels:"
      p @channels
      print " *qvars:"
      p @qvars
      print " *dsyms:"
      p @dsyms
      print " *operators:"
      p @operators
    end
    attr_accessor :nats, :channels, :qvars,
    :dsyms, :operators

    def copy
      ret = NameTable.new
      ret.nats = @nats
      ret.channels = @channels.clone
      ret.qvars = @qvars.clone
      ret.dsyms = @dsyms.clone
      ret.operators = @operators.clone

      ret
    end
  end # class Nametable

  def initialize
    # to be only refered
    @nametable = NameTable.new

    # need to be processed
    @processes = Hash.new
    @environments = Hash.new
    @equations = Hash.new
    @configurations = Hash.new # H[name] = [body_name, env_name]
  end
  attr_accessor :nametable, :processes, :environments,
                :equations, :configurations

  public
  def parse(lexicon)
    while (element = lexicon.shift)
      case element
      when "nat"
        @nametable.nats.push(lexicon.shift)
        unless lexicon.shift == ";"
          raise "nat parse error"
        end
      when "channel"
        channel_name = lexicon.shift
        unless lexicon.shift == ":"
          raise "channel parse error"
        end
        length = lexicon.shift
        unless @nametable.nats.index(length)
          raise "undefined length: " + length
        end
        @nametable.channels[channel_name] = length
        unless lexicon.shift == ";"
          raise "chennel parse error"
        end
      when "qvar"
        qvar_name = lexicon.shift
        unless lexicon.shift == ":"
          raise "qvar parse error"
        end
        length = lexicon.shift
        unless @nametable.nats.index(length)
          raise "undefined length: " + length
        end
        @nametable.qvars[qvar_name] = length
        unless lexicon.shift == ";"
          raise "qvar parse error"
        end
      when "dsym"
        dsym_name = lexicon.shift
        unless lexicon.shift == ":"
          raise "dsym parse error"
        end
        lengths = lexicon.shift.split(",")
        lengths.each { |length_i|
          unless @nametable.nats.index(length_i)
            raise "undefined length: " + length_i
          end
        }
        @nametable.dsyms[dsym_name] = lengths
        unless lexicon.shift == ";"
          raise "dsym parse error"
        end
      when "operator"
        op_name = lexicon.shift
        unless lexicon.shift == ":"
          raise "operator parse error"
        end
        lengths = lexicon.shift.split(",")
        @nametable.operators[op_name] = lengths
        lengths.each { |length_i|
          unless @nametable.nats.index(length_i)
            raise "undefined length: " + length_i
          end
        }
        unless lexicon.shift == ";"
          raise "operator parse error"
        end
      when "process"
        process_name = lexicon.shift
        process_body = String.new
        part = lexicon.shift
        until part == "end"
          if part =~ /meas\Z/
            part = part.gsub!(/meas\Z/, "*meas*")
          end
          if part =~ /\Asaem/
            part = part.gsub!(/\Asaem/, "*saem*")
          end
          process_body += part
          part = lexicon.shift
        end
        @processes[process_name] = process_body
      when "environment"
        environment_name = lexicon.shift
        environment_body = String.new
        part = lexicon.shift
        until part == "end"
          environment_body += part
          part = lexicon.shift
        end
        @environments[environment_name] = environment_body
      when "equation"
        equation_name = lexicon.shift
        equation_body = String.new
        part = lexicon.shift
        until part == "end"
          equation_body += part
          part = lexicon.shift
        end
        @equations[equation_name] = equation_body
      when "configuration"
        configuration_name = lexicon.shift
        unless lexicon.shift == "proc"
          raise "configuration parse error"
        end
        tmp = Array.new
        tmp.push(lexicon.shift)
        unless lexicon.shift == "env"
          raise "configuration parse error"
        end
        tmp.push(lexicon.shift)
        @configurations[configuration_name] = tmp
        unless lexicon.shift == "end"
          raise "configuration parse error"
        end
      else
        raise "parse error, unexpected kind #{element}"
      end #case
    end #while

    # "Tr" is forbidden as operator's name
    # if @nametable.operators["Tr"]
    #   raise "\"Tr\" is forbidden for operator's name"
    # end
    # adversarial computation is denoted *E0, *E1,...
    # operator's name should be start with lowercase
    @nametable.nats.each { |nat|
      unless nat =~ /^[A-z|1-9]/
        raise "#{nat}, nat. symbol should start with alphabet or 1-9 digit"
      end
    }
    @nametable.channels.each { |name, target|
      unless name =~ /^[a-z]/
        raise "#{name}, channel's name should start with lowercase alphabet"
      end
    }
    @nametable.qvars.each { |name, target|
      unless name =~ /^[A-z]/
        raise "#{name}, qvars's name should start with alphabet"
      end
    }
    @nametable.dsyms.each { |name, target|
      unless name =~ /^[A-z]/
        raise "#{name}, qvars's name should start with alphabet"
      end
    }
    @nametable.operators.each { |name, target|
      unless name =~ /^[a-z]/
        raise "#{name}, operator's name should start with lowercase alphabet"
      end
    }
  end

  def show
    puts "**name table**"
    @nametable.show_all;
    puts "**processes**"
    p @processes
    puts "**environments**"
    p @environments
    puts "**equations**"
    p @equations
    puts "**configurations**"
    p @configurations
  end
end
