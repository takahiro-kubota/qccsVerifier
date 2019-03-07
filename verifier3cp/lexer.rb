class Lexer
  public
  def initialize
    @lexicon = Array.new
  end
  attr_accessor :lexicon

  def lex(filename)
    io = open(filename)
    io.each{ |line|
      line.chomp!
      line.strip!
      l = line.gsub(/;/, " ;")
      l = l.gsub(/\s+/, " ")
      tmp = l.split(/ /)
      if tmp[0] == "#"
        next
      end
      @lexicon += tmp
    }
    io.close
  end

  def clear
    initialize
  end

  def show
    puts "***Lexicon***"
    p @lexicon
  end
end
