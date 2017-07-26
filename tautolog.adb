--
-- Copyright (C) 2004   Robert Nowotniak <rnowotniak@gmail.com>
--
-- tautolog.adb - program for checking propositional logic tautologies
-- Jan 26th, 19:53  2004
--
--    This program is free software: you can redistribute it and/or modify
--    it under the terms of the GNU General Public License as published by
--    the Free Software Foundation, either version 3 of the License, or
--    (at your option) any later version.
--
--    This program is distributed in the hope that it will be useful,
--    but WITHOUT ANY WARRANTY; without even the implied warranty of
--    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
--    GNU General Public License for more details.
--
--    You should have received a copy of the GNU General Public License
--    along with this program.  If not, see <http://www.gnu.org/licenses/>.
--
--
-- Logic statements syntax accepted by this program is:
--
--------8<--------8<--------8<--------8<--------8<--------8<--------8<
-- <Sigma> ::= <L> { "<=>" <L> }
-- <L>     ::= <P> { "=>" <P> }
-- <P>     ::= <C> { ( "v" | "^" | "|" | "+" ) <C> }
-- <C>     ::= <Zmien> | <Bool> | '(' <Sigma> ')' | "~" <C>
-- <Zmien> ::= 'a' | 'b' | 'r' | ... | 'u' | 'w' | ... | 'z'
-- <Bool>  ::= ( '0' | 'F' ) | ( '1' | 'P' | 'T' )
--------8<--------8<--------8<--------8<--------8<--------8<--------8<
--
--
-- Operators priorities (from the highest priority to lowest priority):
--
--      [] () {}
--      ~
--      v ^ + |
--      =>
--      <=>
--
--  v   - alternative
--  ^   - conjunction
--  +   - xor
--  |   - Sheffer stroke
--
--
-- Implemented lexical analyser skips all whitespaces and new line characters.
--
--


With Ada.Text_IO;
Use  Ada.Text_IO;
With Ada.Strings.Unbounded;
Use  Ada.Strings.Unbounded;
With Ada.Integer_Text_IO;
Use  Ada.Integer_Text_IO;
With Ada.Strings.Fixed;
Use  Ada.Strings.Fixed;
With GNAT.OS_Lib;

procedure tautolog is


   SYMBOL_ROWNOWAZNOSCI : constant String    := "<=>";
   SYMBOL_IMPLIKACJI    : constant String    := "=>";
   SYMBOL_NEGACJI       : constant String    := "~";
   SYMBOL_KONIUNKCJI    : constant String    := "^";
   SYMBOL_ALTERNATYWY   : constant String    := "v";
   SYMBOL_SCHEFFERA     : constant String    := "|";
   SYMBOL_XOR           : constant String    := "+";

   SYMBOL               : Unbounded_String;
   Linia_Napisu         : Positive := 1;
   Kolumna_Napisu       : Integer  := 1;
   Dobra_Skladnia       : Boolean  := TRUE;
   Ilosc_Dzialan        : Integer  := 0;

   ZLA_SKLADNIA         : exception;


   type Funktor_t is ( Brak, Koniun, Altern, Implik, Rownow, Negacj, Albo, Scheffer );

   type Wezel_t;
   type Wezel_Ptr_t is access Wezel_t;
   type Wezel_t is
      record
         Funk     : Funktor_t;
         Zmienna  : Character;
         Lewy     : Wezel_Ptr_t;
         Prawy    : Wezel_Ptr_t;

         --
         -- Węzły działań mają przyporządkowane liczby porządkowe.
         -- Są one używane do numerowania kolumn w tabelkach
         --
         Lp       : Positive;
      end record;

   --
   -- Węzły listy zmiennych zdaniowych (p, q, r, itp)
   --
   type Wezel_Zmiennej_t;
   type Wezel_Zmiennej_Ptr_t is access Wezel_Zmiennej_t;
   type Wezel_Zmiennej_t is
      record
         Nazwa    : Character := ASCII.NUL;
         Wartosc  : Boolean := FALSE;
         Next     : Wezel_Zmiennej_Ptr_t := null;
      end record;

   Zmienne_Zdaniowe : Wezel_Zmiennej_Ptr_t := null;



   ------------------------------------------------------------
   -- Procedury to obsługi dynamicznie tworzonych węzłów {{{ --
   ------------------------------------------------------------

   --
   -- Używane do rozgałęzień dla funktorów 2-argumentowych
   --
   procedure Utworz_Dwa_Wezly( Ptr : in Wezel_Ptr_t ; Funk : in Funktor_t ) is
      Nowy_Wezel   : Wezel_Ptr_t;
   begin
      Nowy_Wezel      := new Wezel_t;
      Nowy_Wezel.all  := Ptr.all;
      Ptr.all.Funk    := Funk;
      Ptr.all.Zmienna := ASCII.NUL;
      Ptr.all.Lewy    := Nowy_Wezel;
      Ptr.all.Prawy   := new Wezel_t;
   end Utworz_Dwa_Wezly;

   --
   -- Dla przypadku negacji (funktor 1-argumentowy)
   --
   procedure Utworz_Jeden_Wezel( Ptr : in Wezel_Ptr_t ; Funk : in Funktor_t ) is
      Nowy_Wezel   : Wezel_Ptr_t;
   begin
      Nowy_Wezel      := new Wezel_t;
      Nowy_Wezel.all  := Ptr.all;
      Ptr.all.Funk    := Funk;
      Ptr.all.Zmienna := ASCII.NUL;
      Ptr.all.Lewy    := Nowy_Wezel;
      Ptr.all.Prawy   := null;
   end Utworz_Jeden_Wezel;

   --
   -- Zmienne zdaniowe i ich wartości są trzymane w liście
   -- Ta funkcja dodaje element do listy,
   -- o ile takiej zmiennej jeszcze nie ma.
   --
   procedure Dodaj_Zmienna_Zdaniowa( Zmienna: in Character ) is
      Ptr   : Wezel_Zmiennej_Ptr_t := Zmienne_Zdaniowe;
   begin
      if Zmienne_Zdaniowe = null then
         Zmienne_Zdaniowe := new Wezel_Zmiennej_t'(Zmienna, FALSE, null);
         return;
      end if;

      while Ptr.all.Next /= null and Ptr.all.Nazwa /= Zmienna loop
         Ptr := Ptr.all.Next;
      end loop;

      if Ptr.all.Nazwa /= Zmienna then
         Ptr.all.Next := new Wezel_Zmiennej_t'(Zmienna, FALSE, null);
         return;
      end if;
   end Dodaj_Zmienna_Zdaniowa;
   -- }}} -----------------------------------------------------
   ------------------------------------------------------------

   -------------------------------------------------------------
   -- Procedura analizatora leksykalnego (pobiera tokeny) {{{ --
   -------------------------------------------------------------
   procedure Pobierz_Symbol is
      Znak   : Character;
      EOL    : Boolean;
   begin

      SYMBOL := Null_Unbounded_String;

      -- Pominiecie bialych znakow
      Look_Ahead(Znak, EOL);
      while not End_Of_File and then (
         EOL or
         Znak = ' '
         or Znak = ASCII.HT
         or Znak = Character'Val(10)
         or Znak = Character'Val(13) ) loop

         if End_Of_Line then
            Linia_Napisu   := Linia_Napisu + 1;
            Kolumna_Napisu := 1;
            Skip_Line;
         elsif End_Of_Page then
            Skip_Page;
         else
            Kolumna_Napisu := Kolumna_Napisu + 1;
            Get(Znak);
         end if;
         Look_Ahead(Znak, EOL);
      end loop;

      if End_Of_File then
         -- Tutaj nie ma sensu sygnalizować błędu.
         -- Po prostu nie ma już symbolu.
         -- Niech to obsłużą wywołujące funkcje.
         --
         -- Put_Line("Błąd: EOF1");
         return;
      end if;

      Get(Znak);

      if Znak = '^' or Znak = 'v' or Znak = '|' or Znak = '+'
         or Znak = '(' or Znak = ')'
         or Znak = '[' or Znak = ']'
         or Znak = '{' or Znak = '}' then

         SYMBOL := To_Unbounded_String(String'(1=>Znak));
         return;
      end if;

      if Znak in 'a' .. 'z' or Znak in 'A' .. 'Z' then
         Append(SYMBOL, Znak);
         while not End_Of_File and then not End_Of_Line loop
            Look_Ahead(Znak, EOL);
            exit when Znak not in 'a' .. 'z' and Znak not in 'A' .. 'Z';
            Append(SYMBOL, Znak);
            Get(Znak);
         end loop;
         return;
      end if;

      SYMBOL := To_Unbounded_String(String'(1=>Znak));

      if Znak = '<' then
         if End_Of_File then
            return;
         end if;
         Get(Znak);
         if Znak = '=' then
            if End_Of_File then
               return;
            end if;
            Get(Znak);
            if Znak = '>' then
               SYMBOL := To_Unbounded_String("<=>");
               return;
            else
               SYMBOL := To_Unbounded_String("<=");
               return;
            end if;
         end if;
      elsif Znak = '=' then
         if End_Of_File then
            SYMBOL := To_Unbounded_String(String'(1=>Znak));
            return;
         end if;
         Get(Znak);
         if Znak = '>' then
            SYMBOL := To_Unbounded_String("=>");
            return;
         else
            SYMBOL := To_Unbounded_String("=");
            return;
         end if;
      end if;

   end Pobierz_Symbol;
   -- }}} ------------------------------------------------------
   -------------------------------------------------------------

   -------------------------------------------------------------------
   -- Precedury podcelów analizatora składniowego i translatora {{{ --
   -------------------------------------------------------------------

   procedure Nieterminalny_Sigma( Ptr : in Wezel_Ptr_t );
   procedure Nieterminalny_L( Ptr : in Wezel_Ptr_t );
   procedure Nieterminalny_P( Ptr : in Wezel_Ptr_t );
   procedure Nieterminalny_C( Ptr : in Wezel_Ptr_t );
   procedure Nieterminalny_Zmien( Ptr : in Wezel_Ptr_t );
   procedure Nieterminalny_Bool( Ptr : in Wezel_Ptr_t );

   -------------------------------------------------------------------

   --
   -- <Sigma> ::= <L> { "<=>" <L> }
   --
   procedure Nieterminalny_Sigma( Ptr : in Wezel_Ptr_t ) is
   begin
      Nieterminalny_L(Ptr);
      while SYMBOL = SYMBOL_ROWNOWAZNOSCI loop
         Kolumna_Napisu := Kolumna_Napisu + Length(SYMBOL);
         Utworz_Dwa_Wezly(Ptr, Rownow);
         Pobierz_Symbol;
         Nieterminalny_L(Ptr.all.Prawy);
         Ilosc_Dzialan := Ilosc_Dzialan + 1;
         Ptr.Lp := Ilosc_Dzialan;
      end loop;
   end Nieterminalny_Sigma;

   --
   -- <L>     ::= <P> { "=>" <P> }
   --
   procedure Nieterminalny_L( Ptr : in Wezel_Ptr_t ) is
   begin
      Nieterminalny_P(Ptr);
      while SYMBOL = SYMBOL_IMPLIKACJI loop
         Kolumna_Napisu := Kolumna_Napisu + Length(SYMBOL);
         Utworz_Dwa_Wezly(Ptr, Implik);
         Pobierz_Symbol;
         Nieterminalny_P(Ptr.all.Prawy);
         Ilosc_Dzialan := Ilosc_Dzialan + 1;
         Ptr.Lp := Ilosc_Dzialan;
      end loop;
   end Nieterminalny_L;

   --
   -- <P>     ::= <C> { ( "v" | "^" | "|" | "+" ) <C> }
   --
   procedure Nieterminalny_P( Ptr : in Wezel_Ptr_t ) is
   begin
      Nieterminalny_C(Ptr);
      while SYMBOL = SYMBOL_ALTERNATYWY
         or SYMBOL = SYMBOL_KONIUNKCJI
         or SYMBOL = SYMBOL_SCHEFFERA
         or SYMBOL = SYMBOL_XOR
         loop

         if SYMBOL = SYMBOL_ALTERNATYWY then
            Kolumna_Napisu := Kolumna_Napisu + Length(SYMBOL);
            Utworz_Dwa_Wezly(Ptr, Altern);
         elsif SYMBOL = SYMBOL_KONIUNKCJI then
            Kolumna_Napisu := Kolumna_Napisu + Length(SYMBOL);
            Utworz_Dwa_Wezly(Ptr, Koniun);
         elsif SYMBOL = SYMBOL_SCHEFFERA then
            Kolumna_Napisu := Kolumna_Napisu + Length(SYMBOL);
            Utworz_Dwa_Wezly(Ptr, Scheffer);
         elsif SYMBOL = SYMBOL_XOR then
            Kolumna_Napisu := Kolumna_Napisu + Length(SYMBOL);
            Utworz_Dwa_Wezly(Ptr, Albo);
         end if;

         Pobierz_Symbol;
         Nieterminalny_C(Ptr.all.Prawy);
         Ilosc_Dzialan := Ilosc_Dzialan + 1;
         Ptr.Lp := Ilosc_Dzialan;
      end loop;
   end Nieterminalny_P;

   --
   -- <C>     ::= <Zmien> | <Bool> | '(' <Sigma> ')' | "~" <C>
   --
   procedure Nieterminalny_C( Ptr : in Wezel_Ptr_t ) is
      Znak  : Character;
      Blad  : Boolean := FALSE;
   begin

      if Length(SYMBOL) = 1 then

         -- Symbol o długości 1, więc jest szansa
         -- na zmienną, wartość, nawiasy lub negację

         Znak := Element(SYMBOL, 1);
         if Znak in 'a' .. 'u' or else Znak in 'w' .. 'z' then

            -- Jest zmienna
            Nieterminalny_Zmien(Ptr);

         elsif Znak = 'T' or Znak = 'P' or Znak = 'F'
            or Znak = '0' or Znak = '1' then

            -- Jest wartość logiczna
            Nieterminalny_Bool(Ptr);

         elsif Znak = '(' or Znak = '[' or Znak = '{' then

            -- Jest wyrażenie w nawiasach

            Kolumna_Napisu := Kolumna_Napisu + 1;
            Pobierz_Symbol;
            Nieterminalny_Sigma(Ptr);

            if Length(SYMBOL) /= 1 then
               Put_Line("Blad: Spodziewano sie zamkniecia nawiasu");
               Dobra_Skladnia := FALSE;
               raise ZLA_SKLADNIA;
            else
               case Znak is
                  when '(' =>
                     if Element(SYMBOL, 1) /= ')' then
                        Put_Line("Blad: Brakuje )");
                        Dobra_Skladnia := FALSE;
                        raise ZLA_SKLADNIA;
                     else
                        Kolumna_Napisu := Kolumna_Napisu + 1;
                     end if;
                  when '[' =>
                     if Element(SYMBOL, 1) /= ']' then
                        Put_Line("Blad: Brakuje ]");
                        Dobra_Skladnia := FALSE;
                        raise ZLA_SKLADNIA;
                     else
                        Kolumna_Napisu := Kolumna_Napisu + 1;
                     end if;
                  when '{' =>
                     if Element(SYMBOL, 1) /= '}' then
                        Put_Line("Blad: Brakuje }");
                        Dobra_Skladnia := FALSE;
                        raise ZLA_SKLADNIA;
                     else
                        Kolumna_Napisu := Kolumna_Napisu + 1;
                     end if;
                  when Others =>
                     -- Nieosiągalne
                     null;
               end case;
            end if;

            Pobierz_Symbol;
         elsif SYMBOL = SYMBOL_NEGACJI then

            -- Jest negacja
            Pobierz_Symbol;
            Kolumna_Napisu := Kolumna_Napisu + 1;
            Utworz_Jeden_Wezel(Ptr, Negacj);
            Nieterminalny_C(Ptr.all.Lewy);
            Ilosc_Dzialan := Ilosc_Dzialan + 1;
            Ptr.Lp := Ilosc_Dzialan;

         else
            Blad := TRUE;
         end if;
      else
         Blad := TRUE;
      end if;

      if Blad then
         Dobra_Skladnia := FALSE;
         Put_Line("Blad: Zly symbol");
         Put_Line("Blad: Spodziewano sie zmiennej zdaniowej lub wartosci logicznej");
         raise ZLA_SKLADNIA;
      end if;

   end Nieterminalny_C;

   --
   -- <Zmien> ::= 'a' | 'b' | ... | 'p' | 'q' | 'r' | ... | 'u' | 'w' | ... | 'z'
   --
   procedure Nieterminalny_Zmien( Ptr : in Wezel_Ptr_t ) is
      Znak  : Character;
      Blad  : Boolean := FALSE;
   begin

      if Length(SYMBOL) = 1 then
         Znak := Element(SYMBOL, 1);
         if Znak not in 'a' .. 'u' and Znak not in 'w' .. 'z' then
            Blad := TRUE;
            Dobra_Skladnia := FALSE;
         else
            Kolumna_Napisu := Kolumna_Napisu + 1;
            Dodaj_Zmienna_Zdaniowa(Znak);
            Ptr.all.Funk    := Brak;
            Ptr.all.Zmienna := Znak;
            Ptr.all.Prawy   := null;
            Ptr.all.Lewy    := null;
         end if;
      else
         Blad := TRUE;
         Dobra_Skladnia := FALSE;
      end if;

      if Blad then
         Dobra_Skladnia := FALSE;
         Put_Line("Blad: Spodziwano sie zmiennej zdaniowej");
         raise ZLA_SKLADNIA;
      end if;

      Pobierz_Symbol;
   end Nieterminalny_Zmien;

   --
   -- <Bool>  ::= ( '0' | 'F' ) | ( '1' | 'P' | 'T' )
   --
   procedure Nieterminalny_Bool( Ptr : in Wezel_Ptr_t ) is
      Znak  : Character;
      Blad  : Boolean := FALSE;
   begin

      if Length(SYMBOL) = 1 then
         Znak := Element(SYMBOL, 1);
         if Znak /= 'T' and Znak /= 'P'
            and Znak /= 'F' and Znak /= '1' and Znak /= '0' then
            Blad := TRUE;
            Dobra_Skladnia := FALSE;
         else
            Kolumna_Napisu := Kolumna_Napisu + 1;
            Ptr.all.Funk := Brak;
            Ptr.all.Zmienna := Znak;
         end if;
      else
         Blad := TRUE;
         Dobra_Skladnia := FALSE;
      end if;

      if Blad then
         Put_Line("Blad: spodziewano sie wartosci logicznej T lub F.");
         Dobra_Skladnia := FALSE;
         raise ZLA_SKLADNIA;
      end if;

      Pobierz_Symbol;
   end Nieterminalny_Bool;
   -- }}} ------------------------------------------------------------
   -------------------------------------------------------------------

   ------------------------------------------------------------------------------
   -- Procedura wyświetlająca wytworzone drzewo dla wyrażnia (diagnostyka) {{{ --
   ------------------------------------------------------------------------------
   procedure Wyswietl_Drzewo( Ptr: in Wezel_Ptr_t ; Indent : in Integer := 0) is

      function "&"(Str : in String ; Funk : in Funktor_t) return String is
      begin
         case Funk is
            when Brak =>
               return Str & "(brak)";
            when Koniun =>
               return Str & "Koniunkcja";
            when Altern =>
               return Str & "Alternatywa";
            when Implik =>
               return Str & "Implikacja";
            when Rownow =>
               return Str & "Rownowaznosc";
            when Negacj =>
               return Str & "Negacja";
            when Albo =>
               return Str & "Alternatywa wylaczajaca";
            when Scheffer =>
               return Str & "Kreska Scheffera";
         end case;
      end "&";

   begin

      Put(Indent * " ");
      Put_Line("Funktor: " & Ptr.Funk);
      Put(Indent * " ");
      if Ptr.Zmienna /= ASCII.NUL then
         Put_Line("Zmienna: " & Ptr.Zmienna);
      else
         Put_Line("Zmienna: (brak)");
      end if;

      Put(Indent * " ");
      Put_Line("--- lewa galaz");
      if Ptr.Lewy /= null then
         Wyswietl_Drzewo(Ptr.Lewy, Indent + 2);
      else
         Put(Indent * " ");
         Put_Line("NULL");
      end if;

      Put(Indent * " ");
      Put_Line("--- prawa galaz");
      if Ptr.Prawy /= null then
         Wyswietl_Drzewo(Ptr.Prawy, Indent + 2);
      else
         Put(Indent * " ");
         Put_Line("NULL");
      end if;

   end Wyswietl_Drzewo;
   -- }}} -----------------------------------------------------------------------
   ------------------------------------------------------------------------------

   ----------------------------------------------
   -- Funkcje ustalające wartosci logiczne {{{ --
   ----------------------------------------------
   function Wartosc_Zmiennej( Nazwa: in Character ) return Boolean is
      Ptr   : Wezel_Zmiennej_Ptr_t := Zmienne_Zdaniowe;
   begin
      if Ptr = null then
         --
         -- W wygenerowanym drzewie binarnym pojawia się
         -- symbol, który nie znajduje się na liście symboli. (?!?)
         -- To nie powinno i nie mogło nastąpić. (?!?)
         --
         Put_Line("Blad: B1 [to nie powinno wystapic]");
         GNAT.OS_Lib.OS_Exit(2);
      end if;

      while Ptr /= null and then Ptr.all.Nazwa /= Nazwa loop
         Ptr := Ptr.all.Next;
      end loop;

      if Ptr = null or else Ptr.all.Nazwa /= Nazwa then
         --
         -- Ten błąd także nie powinien móc wystąpić
         --
         Put("Blad: Nie jest znana wartosc zmiennej o takiej nazwie(?!?) : ");
         Put(Nazwa);
         Put("Blad: [to nie powinno wystapic]");
         New_Line;
         return False;
      end if;

      return Ptr.all.Wartosc;
   end Wartosc_Zmiennej;


   --
   -- Funkcja zwraca wartość wyrażenia.
   -- Działa rekurencyjnie, przechodzi po drzewie binarnym.
   --
   function Wartosc_Wyr( Ptr: in Wezel_Ptr_t ) return Boolean is

      --
      -- Funktor implikacji jako jedyny trzeba stworzyć samemu
      --
      function Implik( Poprzednik, Nastepnik : in Boolean ) return Boolean is
      begin
         if Poprzednik and not Nastepnik then
            return FALSE;
         else
            return TRUE;
         end if;
      end Implik;

      Ret   : Boolean;

   begin
      case Ptr.all.Funk is
         when Brak =>
            case Ptr.Zmienna is
               when 'T' | 'P' | '1' =>
                  Ret := TRUE;
               when 'F' | '0' =>
                  Ret := FALSE;
               when Others =>
                  Ret := Wartosc_Zmiennej(Ptr.Zmienna);
            end case;

         --
         -- Wykonywanie odpowiednich działań logicznych
         --
         when Koniun =>
            Ret := Wartosc_Wyr(Ptr.Lewy) and Wartosc_Wyr(Ptr.Prawy);
         when Altern =>
            Ret := Wartosc_Wyr(Ptr.Lewy) or Wartosc_Wyr(Ptr.Prawy);
         when Implik =>
            Ret := Implik(Wartosc_Wyr(Ptr.Lewy), Wartosc_Wyr(Ptr.Prawy));
         when Rownow =>
            Ret := Wartosc_Wyr(Ptr.Lewy) = Wartosc_Wyr(Ptr.Prawy);
         when Negacj =>
            Ret := not Wartosc_Wyr(Ptr.Lewy);
         when Albo =>
            Ret := Wartosc_Wyr(Ptr.Lewy) xor Wartosc_Wyr(Ptr.Prawy);
         when Scheffer =>
            Ret := not ( Wartosc_Wyr(Ptr.Lewy) and Wartosc_Wyr(Ptr.Prawy) );
      end case;

      --
      -- Wypisanie zawartości kolumn
      --
      if Ptr.all.Funk /= Brak then
         Put("Kol_");
         Put(Ptr.all.Lp, 1);
         Put(" : ");
         if Ret then
            Put_Line("TAK");
         else
            Put_Line("NIE");
         end if;
      end if;

      return Ret;

   end Wartosc_Wyr;
   -- }}} ---------------------------------------
   ----------------------------------------------

   -----------------------------------------------------------------
   -- Główna procedura pokazująca wartości logiczne wyrażenia {{{ --
   -----------------------------------------------------------------
   procedure Matryca_Logiczna( Korzen: in Wezel_Ptr_t ) is

      --
      -- Ustawianie wartości wszystkich zmiennych zdaniowych na fałsz
      --
      procedure Resetuj_Wartosci( H: in Wezel_Zmiennej_Ptr_t ) is
         Ptr   : Wezel_Zmiennej_Ptr_t := H;
      begin
         while Ptr /= null loop
            Ptr.all.Wartosc := FALSE;
            Ptr := Ptr.all.Next;
         end loop;
      end Resetuj_Wartosci;

      --
      -- Rekurencyjna funkcja zmienia wartości zmiennych, trzymanych w liście,
      -- na kolejną możliwą wartość
      --
      function Zmiana_Wariacji( Ptr: in Wezel_Zmiennej_Ptr_t ) return Boolean is
      begin
         if Ptr = null then
            return TRUE;
         elsif Ptr.all.Next = null or else Zmiana_Wariacji(Ptr.all.Next) then
            if Ptr.all.Wartosc = FALSE then
               Ptr.all.Wartosc := TRUE;
               return FALSE;
            else
               Ptr.all.Wartosc := FALSE;
               return TRUE;
            end if;
         else
            return FALSE;
         end if;
      end Zmiana_Wariacji;


      --
      -- Pokazanie, jakie są wartości logiczne zmiennych,
      -- występujących w sprawdzanym wyrażeniu
      --
      procedure Pokaz_Wartosci is
         Ptr      : Wezel_Zmiennej_Ptr_t := Zmienne_Zdaniowe;
      begin
         while Ptr /= null loop
            Put("  ");
            if Ptr.all.Wartosc then
               Put("1");
            else
               Put("0");
            end if;
            Ptr := Ptr.all.Next;
         end loop;
      end Pokaz_Wartosci;


      --
      -- Procedura pokazuje, jakby ,,legendę'' kolumn,
      -- jakie zdanie proste znajduje się w danej kolumnie w tabelce
      --
      procedure Pokaz_Naglowek is

         -- rekurencyjnie
         procedure Pokaz( Ptr: in Wezel_Ptr_t ) is

            --
            -- Przeciążone Put() do wypisania funktora
            --
            procedure Put( Funk : in Funktor_t ) is
            begin
               case Funk is
                  when Brak =>
                     Put("(brak)");
                  when Koniun =>
                     Put(SYMBOL_KONIUNKCJI);
                  when Altern =>
                     Put(SYMBOL_ALTERNATYWY);
                  when Implik =>
                     Put(SYMBOL_IMPLIKACJI);
                  when Rownow =>
                     Put(SYMBOL_ROWNOWAZNOSCI);
                  when Negacj =>
                     Put(SYMBOL_NEGACJI);
                  when Albo =>
                     Put(SYMBOL_XOR);
                  when Scheffer =>
                     Put(SYMBOL_SCHEFFERA);
               end case;
            end Put;

         begin
            if Ptr.Lewy /= null and then Ptr.Lewy.Funk /= Brak then
               Pokaz(Ptr.Lewy);
            end if;
            if Ptr.Prawy /= null and then Ptr.Prawy.Funk /= Brak then
               Pokaz(Ptr.Prawy);
            end if;
            if Ptr.Funk = Negacj then
               Put("Kol_");
               Put(Ptr.Lp, 1);
               Put(" : ");
               Put(SYMBOL_NEGACJI);
               Put(" ");
               if Ptr.Lewy.Funk /= Brak then
                  Put("Kol_");
                  Put(Ptr.Lewy.Lp, 1);
               else
                  Put(Ptr.Lewy.Zmienna);
               end if;
               New_Line;
            elsif Ptr.Funk /= Brak then
               Put("Kol_");
               Put(Ptr.Lp, 1);
               Put(" : ");
               if Ptr.Lewy.Funk /= Brak then
                  Put("Kol_");
                  Put(Ptr.Lewy.Lp, 1);
               else
                  Put(Ptr.Lewy.Zmienna);
               end if;

               Put(" "); Put(Ptr.Funk); Put(" ");

               if Ptr.Prawy.Funk /= Brak then
                  Put("Kol_");
                  Put(Ptr.Prawy.Lp, 1);
               else
                  Put(Ptr.Prawy.Zmienna);
               end if;
               New_Line;
            end if;
         end Pokaz;

      begin
         Pokaz(Korzen);
      end Pokaz_Naglowek;


      -- Wartość wynikowa sprawdzanego wyrażenia
      Wynik   : Boolean;

   begin

      -- Ten nagłówek to niemal jak ,,legenda mapy'' (numery kolumn)
      Pokaz_Naglowek;
      New_Line;
      New_Line;


      --
      -- Przestawianie wartości zmiennych po kolej,
      -- obliczanie wartości logicznych, wyświetlanie
      --

      Resetuj_Wartosci(Zmienne_Zdaniowe);
      Put_Line("*----");
      Wynik := Wartosc_Wyr(Korzen);
      Pokaz_Wartosci;

      if Wynik then
         Put("    TAK");
      else
         Put("    NIE");
      end if;
      New_Line;
      Put_Line("*----");

      while not Zmiana_Wariacji(Zmienne_Zdaniowe) loop
         Wynik := Wartosc_Wyr(Korzen);
         Pokaz_Wartosci;
         if Wynik then
            Put("    TAK");
         else
            Put("    NIE");
         end if;
         New_Line;
         Put_Line("*----");
      end loop;
   end Matryca_Logiczna;
   -- }}} ----------------------------------------------------------
   -----------------------------------------------------------------

   --
   -- Wyświetla po prostu, jakie są nazwy zmiennych zdaniowych,
   -- pojawiających się w badanym wyrażeniu
   --
   procedure Pokaz_Zmienne_Zdaniowe is
      Ptr   : Wezel_Zmiennej_Ptr_t := Zmienne_Zdaniowe;
   begin
      Put_Line("Zmienne zdaniowe:");
      while Ptr /= null loop
         Put(Ptr.Nazwa & " ");
         Ptr := Ptr.Next;
      end loop;
      New_Line;
   end Pokaz_Zmienne_Zdaniowe;


   --
   -- Korzeń drzewa binarnego,
   -- które reprezentuje wyrażenie zdaniowe
   --
   Korzen  : Wezel_Ptr_t := new Wezel_t;

begin

   begin
      --
      -- Analiza składniowa, translacja na drzewo
      --
      Pobierz_Symbol;
      Nieterminalny_Sigma(Korzen);
   exception
      when ZLA_SKLADNIA =>
         -- Dzięki wyjątkowi był wyskok.
         -- Nic robić nie trzeba.
         null;
   end;

   if Dobra_Skladnia and SYMBOL /= Null_Unbounded_String then
      Dobra_Skladnia := FALSE;
      Put_Line("Blad: Po napisie cos nastepuje.");
   end if;

   if not Dobra_Skladnia then
      Put_Line("Linia:   "  & Integer'Image(Linia_Napisu));
      Put_Line("Kolumna: "  & Integer'Image(Kolumna_Napisu));
      Put_Line("Symbol:   " & To_String(SYMBOL));
      GNAT.OS_Lib.OS_Exit(1);
   end if;

-- Wyswietl_Drzewo(Korzen);

   Put_Line("Syntax OK.");

   New_Line;
   Pokaz_Zmienne_Zdaniowe;

   New_Line;
   Matryca_Logiczna(Korzen);

   GNAT.OS_Lib.OS_Exit(0);

end tautolog;


--  vim: set fdm=marker fmr& fdl=0:
