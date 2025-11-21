// mesh_uvm_pkg.sv
//
// Package UVM para la malla 4x4.
// Contiene:
//   - Tipo de modo de ruteo
//   - Transacción mesh_packet (sequence_item)
//   - Secuencia base
//   - Secuencias de pruebas generales:
//       * Conectividad aleatoria
//       * Comparación de modos de ruta
//       * Broadcast funcional
//   - Secuencias de casos de esquina:
//       * Broadcast desde una esquina
//       * FIFO llena y back-pressure
//       * Ruta máxima esquina a esquina
//       * Contención fuerte y todos los puertos activos
//       * Arbitraje moderado hacia un mismo destino
//       * Router como terminal y destino

package mesh_uvm_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  

  // ------------------------------------------------------------
  // 1) Enumeración de modos de ruta (a nivel de transacción)
  // ------------------------------------------------------------
  //
  // La codificación interna del DUT puede ser distinta.
  // El driver se encargará de mapear este enum al bit "Mode"
  // y cualquier otro campo necesario en el paquete de 40 bits.
  //
  typedef enum bit [1:0] {
    MESH_MODE_ROW_FIRST = 2'b00,  // fila primero
    MESH_MODE_COL_FIRST = 2'b01,  // columna primero
    MESH_MODE_BCAST     = 2'b10   // broadcast
  } mesh_mode_e;

  // ------------------------------------------------------------
  // 2) Clase de transacción: mesh_packet
  // ------------------------------------------------------------
  //
  // Representa el paquete de 40 bits a nivel de UVM:
  //
  // Campos del paquete físico (según testplan):
  //   [39:32] Nxt jump     -> lo escribe el router (Internal Interface ID)
  //   [31:28] Row          -> parte del External Interface ID
  //   [27:24] Column       -> parte del External Interface ID
  //   [23]    Mode         -> modo de ruteo (fila/columna/broadcast)
  //   [22:0]  Payload      -> mensaje
  //
  // Además agregamos:
  //   - src_term: terminal origen en la malla (0 a 15)
  //   - dst_term: terminal destino esperado (0 a 15)
  //   - delay_cycles: retardo entre transacciones (3 a 5 ciclos)
  //   - meta datos opcionales para scoreboard (tiempos, hops, etc)
  //

  // Typedef para el virtual interface usado por drivers y monitores
  typedef virtual mesh_if mesh_vif_t;

  class mesh_packet extends uvm_sequence_item;

    // Terminal origen en la malla (0..15)
    rand int unsigned src_term;

    // Coordenadas de destino según External Interface ID
    // Estas se usan para generar Row/Column y luego el driver las codifica.
    rand bit [3:0] dst_row;
    rand bit [3:0] dst_col;

    // Modo de ruteo a nivel abstracto
    rand mesh_mode_e mode;

    // Payload de 23 bits (se puede subdividir mas adelante si hace falta)
    rand bit [22:0] payload;

    // Campo Nxt jump (8 bits) lo rellena el DUT, por eso no es rand
    bit  [7:0] nxt_jump;

    // Terminal destino esperado (derivado de Row/Column).
    // El driver o el scoreboard pueden calcularlo, pero lo dejamos aqui por claridad.
    int unsigned dst_term;

    // Retardo entre esta transacción y la siguiente (en ciclos de reloj)
    rand int unsigned delay_cycles;

    // Metadatos utiles para scoreboard (no obligatorios, pero ayudan)
    time send_time;   // tiempo cuando el driver inyecta el paquete
    time recv_time;   // tiempo cuando el monitor ve el paquete en destino
    int  exp_hops;    // numero de saltos esperados (scoreboard lo puede calcular)

    // ----------------------------------------------------------
    // Registro UVM y macros de automatizacion de campos
    // ----------------------------------------------------------
    `uvm_object_utils_begin(mesh_packet)
      `uvm_field_int(src_term,     UVM_ALL_ON)
      `uvm_field_int(dst_row,      UVM_ALL_ON)
      `uvm_field_int(dst_col,      UVM_ALL_ON)
      `uvm_field_enum(mesh_mode_e, mode,        UVM_ALL_ON)
      `uvm_field_int(payload,      UVM_ALL_ON)
      `uvm_field_int(nxt_jump,     UVM_ALL_ON | UVM_READONLY)
      `uvm_field_int(dst_term,     UVM_ALL_ON)
      `uvm_field_int(delay_cycles, UVM_ALL_ON)
      `uvm_field_int(send_time,    UVM_NOPACK)   // meta, no se empaca
      `uvm_field_int(recv_time,    UVM_NOPACK)
      `uvm_field_int(exp_hops,     UVM_ALL_ON)
    `uvm_object_utils_end

    // ----------------------------------------------------------
    // Constructor
    // ----------------------------------------------------------
    function new(string name = "mesh_packet");
      super.new(name);
    endfunction

    // ----------------------------------------------------------
    // Constraints genericos
    // ----------------------------------------------------------

    // Rango basico para las terminales externas
    constraint c_src_term_range {
      src_term inside {[0:15]};
    }

    // Rango basico para filas y columnas
    // Aqui asumimos que las filas y columnas validas estan entre 0 y 5,
    // luego podemos restringirlas al conjunto exacto de External Interface ID.
    constraint c_row_col_range {
      dst_row inside {[0:5]};
      dst_col inside {[0:5]};
    }

    // Retardo entre transacciones segun testplan: 3 a 5 ciclos
    constraint c_delay {
      delay_cycles inside {[3:5]};
    }

    // Constraint para destinos validos en la malla,
    // basado en los External Interface ID:
    //
    //   01,02,03,04
    //   10,20,30,40
    //   51,52,53,54
    //   15,25,35,45
    //
    constraint c_legal_external_id {
      {dst_row, dst_col} inside {
        {4'd0, 4'd1}, {4'd0, 4'd2}, {4'd0, 4'd3}, {4'd0, 4'd4},  // 01,02,03,04
        {4'd1, 4'd0}, {4'd2, 4'd0}, {4'd3, 4'd0}, {4'd4, 4'd0},  // 10,20,30,40
        {4'd5, 4'd1}, {4'd5, 4'd2}, {4'd5, 4'd3}, {4'd5, 4'd4},  // 51,52,53,54
        {4'd1, 4'd5}, {4'd2, 4'd5}, {4'd3, 4'd5}, {4'd4, 4'd5}   // 15,25,35,45
      };
    }

    // Metodo helper opcional: convierte los campos a un vector de 40 bits.
    function bit [39:0] to_bits();
      bit [39:0] pkt;
      pkt = '0;
      pkt[39:32] = nxt_jump;       // lo llenara el DUT, aqui puede ir en 0
      pkt[31:28] = dst_row;
      pkt[27:24] = dst_col;
      pkt[23]    = (mode == MESH_MODE_ROW_FIRST) ? 1'b1 :
                   (mode == MESH_MODE_COL_FIRST) ? 1'b0 :
                   1'b1; // para broadcast se puede definir luego
      pkt[22:0]  = payload;
      return pkt;
    endfunction

  endclass : mesh_packet

  // ------------------------------------------------------------
  // 3) Secuencia base: mesh_base_seq
  // ------------------------------------------------------------
  class mesh_base_seq extends uvm_sequence #(mesh_packet);

    `uvm_object_utils(mesh_base_seq)

    function new(string name = "mesh_base_seq");
      super.new(name);
    endfunction

    virtual task body();
      // Esta secuencia base no genera trafico por si sola.
      // Las secuencias derivadas implementan sus propios patrones.
    endtask

  endclass : mesh_base_seq

  // ------------------------------------------------------------
  // 4) Secuencia: Conectividad aleatoria
  // ------------------------------------------------------------
  class mesh_rand_connectivity_seq extends mesh_base_seq;

    `uvm_object_utils(mesh_rand_connectivity_seq)

    // Numero total de paquetes que queremos enviar en esta prueba
    rand int unsigned num_packets;

    // Numero maximo de terminales origen diferentes que se activan a la vez
    rand int unsigned num_active_src_terms;

    // Constraint: rango razonable de paquetes
    constraint c_num_packets {
      num_packets inside {[20:40]};  // ajustable
    }

    // Constraint: de 1 a 8 terminales activas
    constraint c_num_active_src_terms {
      num_active_src_terms inside {[1:8]};
    }

    function new(string name = "mesh_rand_connectivity_seq");
      super.new(name);
    endfunction

    virtual task body();
      mesh_packet tr;

      `uvm_info(get_type_name(),
                $sformatf("Iniciando Conectividad aleatoria: num_packets=%0d",
                          num_packets),
                UVM_MEDIUM)

      // Randomizar los parametros de la secuencia
      if (!randomize()) begin
        `uvm_error(get_type_name(), "Fallo randomize() en mesh_rand_connectivity_seq")
        return;
      end

      // Version simple: cada transaccion escoge src_term aleatoriamente.
      for (int n = 0; n < num_packets; n++) begin

        tr = mesh_packet::type_id::create($sformatf("tr_%0d", n), null);

        if (!tr.randomize() with {
              // En conectividad aleatoria evitamos broadcast para esta prueba:
              mode inside {MESH_MODE_ROW_FIRST, MESH_MODE_COL_FIRST};
            }) begin
          `uvm_error(get_type_name(), "Fallo randomize() de mesh_packet en conectividad aleatoria")
          continue;
        end

        start_item(tr);
        finish_item(tr);

        `uvm_info(get_type_name(),
                  $sformatf("Enviando paquete aleatorio %0d: src_term=%0d row=%0d col=%0d mode=%0d payload=0x%0h delay=%0d",
                            n, tr.src_term, tr.dst_row, tr.dst_col, tr.mode, tr.payload, tr.delay_cycles),
                  UVM_LOW)
      end

      `uvm_info(get_type_name(),
                "Finalizando Conectividad aleatoria",
                UVM_MEDIUM)
    endtask

  endclass : mesh_rand_connectivity_seq

  // ------------------------------------------------------------
  // 5) Secuencia: Comparacion de modos de ruta
  // ------------------------------------------------------------
  class mesh_compare_modes_seq extends mesh_base_seq;

    `uvm_object_utils(mesh_compare_modes_seq)

    // Numero de repeticiones por par origen-destino
    rand int unsigned num_reps_per_pair;

    constraint c_num_reps {
      num_reps_per_pair inside {[1:5]};
    }

    function new(string name = "mesh_compare_modes_seq");
      super.new(name);
    endfunction

  virtual task body();
    mesh_packet tr_row_first;
    mesh_packet tr_col_first;

    // Declaraciones locales (antes de cualquier sentencia ejecutable)
    int unsigned src_terms[$];
    bit [3:0]    dst_rows[$];
    bit [3:0]    dst_cols[$];
    int unsigned rep;

    // Randomizar parámetros de la secuencia
    if (!randomize()) begin
      `uvm_error(get_type_name(), "Fallo randomize() en mesh_compare_modes_seq")
      return;
    end

    `uvm_info(get_type_name(),
              $sformatf("Iniciando Comparacion de modos de ruta: num_reps_per_pair=%0d",
                        num_reps_per_pair),
              UVM_MEDIUM)

    // Lista de pares esquina a esquina (ejemplo, se puede ajustar):
    //
    // Supongamos que:
    //   - src_term 0 corresponde a una esquina (ej. UP de router (1,1))
    //   - src_term 3 a otra esquina, etc.
    // Ajusta estos valores según tu mapeo real.
    //
    src_terms = '{0, 3, 12, 15};                     // terminales de origen
    dst_rows  = '{4'd5, 4'd0, 4'd5, 4'd0};           // filas destino
    dst_cols  = '{4'd4, 4'd1, 4'd5, 4'd4};           // columnas destino

    foreach (src_terms[idx]) begin
      for (rep = 0; rep < num_reps_per_pair; rep++) begin

        // Paquete con modo fila primero
        tr_row_first = mesh_packet::type_id::create(
          $sformatf("tr_row_first_s%0d_rep%0d", idx, rep), null);

        if (!tr_row_first.randomize() with {
              src_term == src_terms[idx];
              dst_row  == dst_rows[idx];
              dst_col  == dst_cols[idx];
              mode     == MESH_MODE_ROW_FIRST;
            }) begin
          `uvm_error(get_type_name(), "Fallo randomize() tr_row_first")
          continue;
        end

        start_item(tr_row_first);
        finish_item(tr_row_first);

        `uvm_info(get_type_name(),
                  $sformatf("Modo fila primero: src_term=%0d row=%0d col=%0d payload=0x%0h",
                            tr_row_first.src_term, tr_row_first.dst_row,
                            tr_row_first.dst_col, tr_row_first.payload),
                  UVM_LOW)

        // Paquete con modo columna primero
        tr_col_first = mesh_packet::type_id::create(
          $sformatf("tr_col_first_s%0d_rep%0d", idx, rep), null);

        if (!tr_col_first.randomize() with {
              src_term == src_terms[idx];
              dst_row  == dst_rows[idx];
              dst_col  == dst_cols[idx];
              mode     == MESH_MODE_COL_FIRST;
            }) begin
          `uvm_error(get_type_name(), "Fallo randomize() tr_col_first")
          continue;
        end

        start_item(tr_col_first);
        finish_item(tr_col_first);

        `uvm_info(get_type_name(),
                  $sformatf("Modo columna primero: src_term=%0d row=%0d col=%0d payload=0x%0h",
                            tr_col_first.src_term, tr_col_first.dst_row,
                            tr_col_first.dst_col, tr_col_first.payload),
                  UVM_LOW)
      end
    end

    `uvm_info(get_type_name(),
              "Finalizando Comparacion de modos de ruta",
              UVM_MEDIUM)
  endtask


  endclass : mesh_compare_modes_seq

  // ------------------------------------------------------------
  // 6) Secuencia: Broadcast funcional
  // ------------------------------------------------------------
  class mesh_broadcast_seq extends mesh_base_seq;

    `uvm_object_utils(mesh_broadcast_seq)

    // Numero de paquetes broadcast a enviar desde la misma fuente
    rand int unsigned num_bcast_packets;

    constraint c_num_bcast {
      num_bcast_packets inside {[1:10]};
    }

    function new(string name = "mesh_broadcast_seq");
      super.new(name);
    endfunction

    virtual task body();
      mesh_packet tr;
      int unsigned src_bcast_term;

      if (!randomize()) begin
        `uvm_error(get_type_name(), "Fallo randomize() en mesh_broadcast_seq")
        return;
      end

      // Elegimos un origen para broadcast (0..15).
      void'(std::randomize(src_bcast_term) with { src_bcast_term inside {[0:15]}; });

      `uvm_info(get_type_name(),
                $sformatf("Iniciando Broadcast funcional: num_bcast_packets=%0d src_bcast_term=%0d",
                          num_bcast_packets, src_bcast_term),
                UVM_MEDIUM)

      for (int n = 0; n < num_bcast_packets; n++) begin

        tr = mesh_packet::type_id::create($sformatf("bcast_tr_%0d", n), null);

        if (!tr.randomize() with {
              src_term    == src_bcast_term;
              mode        == MESH_MODE_BCAST;
            }) begin
          `uvm_error(get_type_name(), "Fallo randomize() en mesh_broadcast_seq")
          continue;
        end

        start_item(tr);
        finish_item(tr);

        `uvm_info(get_type_name(),
                  $sformatf("Enviando broadcast %0d desde src_term=%0d, payload=0x%0h, delay=%0d",
                            n, tr.src_term, tr.payload, tr.delay_cycles),
                  UVM_LOW)
      end

      `uvm_info(get_type_name(),
                "Finalizando Broadcast funcional",
                UVM_MEDIUM)
    endtask

  endclass : mesh_broadcast_seq

  // ==================================================================
  // 7) Secuencia de caso de esquina: Broadcast desde una esquina
  // ==================================================================
  //
  // Testplan:
  //   "Broadcast desde una esquina"
  //
  // Objetivo:
  //   - Enviar un paquete broadcast desde una terminal de esquina.
  //   - Verificar que se propaga a toda la malla y llega a todas
  //     las terminales externas salvo el origen.
  //
  // Estrategia:
  //   - Se restringe la terminal de origen a un conjunto de esquinas.
  //   - Se envian varios paquetes en modo broadcast.
  //   - El scoreboard debe comprobar que todas las terminales reciben
  //     el payload y que no hay perdidas ni bloqueos.
  //
  class mesh_corner_bcast_seq extends mesh_base_seq;

    `uvm_object_utils(mesh_corner_bcast_seq)

    // Numero de paquetes broadcast enviados desde la esquina
    rand int unsigned num_bcast_packets;

    constraint c_num_bcast_corner {
      num_bcast_packets inside {[1:5]};
    }

    // Conjunto de terminales de esquina (ejemplo, ajustar a mapping real)
    int unsigned corner_terms[$] = '{0, 3, 12, 15, 11, 8, 4};
 
    function new(string name = "mesh_corner_bcast_seq");
      super.new(name);
    endfunction

    virtual task body();
      mesh_packet tr;
      int unsigned src_corner_idx;
      int unsigned src_corner_term;

      if (!randomize()) begin
        `uvm_error(get_type_name(), "Fallo randomize() en mesh_corner_bcast_seq")
        return;
      end

      // Elegimos una esquina aleatoria del arreglo corner_terms
      void'(std::randomize(src_corner_idx) with {
        src_corner_idx inside {[0:corner_terms.size()-1]};
      });
      src_corner_term = corner_terms[src_corner_idx];

      `uvm_info(get_type_name(),
                $sformatf("Broadcast desde esquina: src_corner_term=%0d, num_bcast_packets=%0d",
                          src_corner_term, num_bcast_packets),
                UVM_MEDIUM)

      for (int n = 0; n < num_bcast_packets; n++) begin
        tr = mesh_packet::type_id::create($sformatf("corner_bcast_%0d", n), null);

        if (!tr.randomize() with {
              src_term == src_corner_term;
              mode     == MESH_MODE_BCAST;
            }) begin
          `uvm_error(get_type_name(), "Fallo randomize() en mesh_corner_bcast_seq")
          continue;
        end

        start_item(tr);
        finish_item(tr);

        `uvm_info(get_type_name(),
                  $sformatf("Corner broadcast %0d desde src_term=%0d payload=0x%0h delay=%0d",
                            n, tr.src_term, tr.payload, tr.delay_cycles),
                  UVM_LOW)
      end

      `uvm_info(get_type_name(),
                "Finalizando Broadcast desde una esquina",
                UVM_MEDIUM)
    endtask

  endclass : mesh_corner_bcast_seq

  // ==================================================================
  // 8) Secuencia de caso de esquina: FIFO llena y back-pressure
  // ==================================================================
  //
  // Testplan:
  //   "FIFO llena y back-pressure"
  //
  // Objetivo:
  //   - Forzar las FIFOs internas a su capacidad maxima.
  //   - Observar que el diseño aplica back-pressure, no acepta mas
  //     paquetes y no se pierden datos.
  //
  // Estrategia de la secuencia:
  //   - Enviar trafico continuo desde uno o varios origenes
  //     hacia un conjunto reducido de destinos (hotspots).
  //   - El ambiente UVM (driver/monitor/scoreboard) se configurara
  //     para retrasar o inhibir pops en las salidas para provocar
  //     el llenado de las FIFOs.
  //   - Esta secuencia solo define el patron de trafico denso.
  //
  class mesh_fifo_full_backpressure_seq extends mesh_base_seq;

    `uvm_object_utils(mesh_fifo_full_backpressure_seq)

    // Numero de terminales fuente activas que saturan la red
    rand int unsigned num_src_terms;

    // Numero de paquetes por cada fuente
    rand int unsigned num_packets_per_src;

    // Lista de destinos "calientes" para concentrar trafico
    rand int unsigned num_hotspot_dests;

    // Constraints basicos
    constraint c_num_src_terms {
      num_src_terms inside {[2:8]};         // de 2 a 8 fuentes
    }

    constraint c_num_packets_per_src {
      num_packets_per_src inside {[5:15]};  // varios paquetes por fuente
    }

    constraint c_num_hotspot_dests {
      num_hotspot_dests inside {[1:3]};     // 1 a 3 destinos calientes
    }

    function new(string name = "mesh_fifo_full_backpressure_seq");
      super.new(name);
    endfunction

  virtual task body();
    mesh_packet tr;

    // Declaraciones PRIMERO (antes de cualquier sentencia ejecutable)
    int unsigned src_terms[$];      // lista de fuentes activas
    int unsigned candidate;         // candidato a fuente

    bit [3:0] hotspot_rows[$];      // filas de destinos hotspot
    bit [3:0] hotspot_cols[$];      // columnas de destinos hotspot

    bit [3:0] r, c;                 // variables temporales para elegir hotspot
    bit       found;                // flag para evitar hotspots duplicados

    int unsigned h_idx;             // índice de hotspot
    int         p;                  // índice del paquete en el for
    int         s_idx;              // índice de la fuente en foreach

    // Randomizar parámetros de la secuencia
    if (!randomize()) begin
      `uvm_error(get_type_name(), "Fallo randomize() en mesh_fifo_full_backpressure_seq")
      return;
    end

    // Construimos lista de fuentes activas sin repetir
    while (src_terms.size() < num_src_terms) begin
      void'(std::randomize(candidate) with { candidate inside {[0:15]}; });
      if (!(candidate inside {src_terms})) begin
        src_terms.push_back(candidate);
      end
    end

    // Construimos lista de destinos calientes como pares (row,col)
    while (hotspot_rows.size() < num_hotspot_dests) begin
      // Elegimos un par (r,c) legal en la malla exterior
      void'(std::randomize(r, c) with {
        {r, c} inside {
          {4'd0, 4'd1}, {4'd0, 4'd2}, {4'd0, 4'd3}, {4'd0, 4'd4},
          {4'd1, 4'd0}, {4'd2, 4'd0}, {4'd3, 4'd0}, {4'd4, 4'd0},
          {4'd5, 4'd1}, {4'd5, 4'd2}, {4'd5, 4'd3}, {4'd5, 4'd4},
          {4'd1, 4'd5}, {4'd2, 4'd5}, {4'd3, 4'd5}, {4'd4, 4'd5}
        };
      });

      // Verificar que no esté repetido
      found = 1'b0;
      foreach (hotspot_rows[i]) begin
        if (hotspot_rows[i] == r && hotspot_cols[i] == c)
          found = 1'b1;
      end

      if (!found) begin
        hotspot_rows.push_back(r);
        hotspot_cols.push_back(c);
      end
    end

    `uvm_info(get_type_name(),
              $sformatf("FIFO llena/back-pressure: num_src_terms=%0d num_packets_per_src=%0d num_hotspots=%0d",
                        num_src_terms, num_packets_per_src, num_hotspot_dests),
              UVM_MEDIUM)

    // Patrón de tráfico intenso: cada fuente envía muchos paquetes
    // concentrados en los destinos hotspot.
    foreach (src_terms[s_idx]) begin
      for (p = 0; p < num_packets_per_src; p++) begin

        tr = mesh_packet::type_id::create(
          $sformatf("fifo_full_src%0d_pkt%0d", src_terms[s_idx], p), null);

        // Elegimos uno de los destinos hotspot
        void'(std::randomize(h_idx) with {
          h_idx inside {[0:hotspot_rows.size()-1]};
        });

        if (!tr.randomize() with {
              src_term == src_terms[s_idx];
              dst_row  == hotspot_rows[h_idx];
              dst_col  == hotspot_cols[h_idx];
              mode     inside {MESH_MODE_ROW_FIRST, MESH_MODE_COL_FIRST};
            }) begin
          `uvm_error(get_type_name(), "Fallo randomize() en fifo_full_backpressure")
          continue;
        end

        start_item(tr);
        finish_item(tr);

        `uvm_info(get_type_name(),
                  $sformatf("FIFO-full: src=%0d -> row=%0d col=%0d payload=0x%0h delay=%0d",
                            tr.src_term, tr.dst_row, tr.dst_col,
                            tr.payload, tr.delay_cycles),
                  UVM_LOW)
      end
    end

    `uvm_info(get_type_name(),
              "Finalizando FIFO llena y back-pressure",
              UVM_MEDIUM)
  endtask


  endclass : mesh_fifo_full_backpressure_seq

  // ==================================================================
  // 9) Secuencia de caso de esquina: Ruta máxima esquina a esquina
  // ==================================================================
  //
  // Testplan:
  //   "Ruta máxima esquina a esquina"
  //
  // Objetivo:
  //   - Enviar paquetes desde una esquina hacia la esquina opuesta
  //     recorriendo la ruta mas larga posible.
  //   - Medir latencia y numero de saltos.
  //
  // Estrategia:
  //   - Se seleccionan pares esquina-opuesta (segun mapping).
  //   - Para cada par se enviaran varios paquetes con un modo de ruteo
  //     (fila primero o columna primero, o ambos dependiendo del test).
  //   - El scoreboard usa los campos send_time, recv_time y exp_hops.
  //
  class mesh_max_corner_path_seq extends mesh_base_seq;

    `uvm_object_utils(mesh_max_corner_path_seq)

    // Numero de paquetes por cada par esquina-esquina
    rand int unsigned num_packets_per_pair;

    constraint c_num_packets_per_pair {
      num_packets_per_pair inside {[6:10]};
    }

    function new(string name = "mesh_max_corner_path_seq");
      super.new(name);
    endfunction

  virtual task body();
    // Declaraciones PRIMERO
    mesh_packet tr;

    // Listas de pares esquina-opuesta
    int unsigned src_terms[$];
    bit [3:0]    dst_rows[$];
    bit [3:0]    dst_cols[$];

    int n;   // índice del for
    int idx; // índice del foreach (implícito, pero lo declaramos por claridad)

    // Inicializamos las listas (esto ya son sentencias, no declaraciones)
    src_terms = '{0, 3, 12, 15};
    dst_rows  = '{4'd5, 4'd0, 4'd5, 4'd0};
    dst_cols  = '{4'd4, 4'd1, 4'd5, 4'd4};

    // Randomizamos los parámetros de la secuencia
    if (!randomize()) begin
      `uvm_error(get_type_name(), "Fallo randomize() en mesh_max_corner_path_seq")
      return;
    end

    `uvm_info(get_type_name(),
              $sformatf("Iniciando Ruta maxima esquina a esquina: num_packets_per_pair=%0d",
                        num_packets_per_pair),
              UVM_MEDIUM)

    // Lista de ejemplos de pares esquina-opuesta
    // Ajustar según mapping real de src_term y External IDs.
    foreach (src_terms[idx]) begin
      for (n = 0; n < num_packets_per_pair; n++) begin
        tr = mesh_packet::type_id::create(
          $sformatf("max_path_s%0d_pkt%0d", idx, n), null);

        if (!tr.randomize() with {
              src_term == src_terms[idx];
              dst_row  == dst_rows[idx];
              dst_col  == dst_cols[idx];
              // Se alterna modo fila/columna primero de forma aleatoria
              mode inside {MESH_MODE_ROW_FIRST, MESH_MODE_COL_FIRST};
            }) begin
          `uvm_error(get_type_name(), "Fallo randomize() en max_corner_path")
          continue;
        end

        // exp_hops podría rellenarse aquí si conoces el número esperado
        // para este par, para que el scoreboard compare.
        // tr.exp_hops = <valor esperado>;

        start_item(tr);
        finish_item(tr);

        `uvm_info(get_type_name(),
                  $sformatf("Max path: src=%0d -> row=%0d col=%0d mode=%0d payload=0x%0h delay=%0d",
                            tr.src_term, tr.dst_row, tr.dst_col,
                            tr.mode, tr.payload, tr.delay_cycles),
                  UVM_LOW)
      end
    end

    `uvm_info(get_type_name(),
              "Finalizando Ruta maxima esquina a esquina",
              UVM_MEDIUM)
  endtask


  endclass : mesh_max_corner_path_seq



  // ==================================================================
  // 10) Secuencia de caso de esquina:
  //     Contención fuerte y todos los puertos activos
  // ==================================================================
  //
  // Testplan:
  //   "Contención fuerte y todos los puertos activos"
  //
  // Objetivo:
  //   - Someter el sistema a carga maxima.
  //   - Variante 1: varios origenes hacia pocos destinos (hotspot).
  //   - Variante 2: todos los puertos activos con destinos variados.
  //
  // Estrategia de secuencia:
  //   - Activar todas o casi todas las terminales como fuentes.
  //   - Enviar muchos paquetes por cada fuente.
  //   - Alternar entre un comportamiento de hotspot (2–3 destinos)
  //     y destinos dispersos por toda la malla.
  //   - El scoreboard debe comprobar que no hay deadlocks ni starvation.
  //
  class mesh_full_load_contention_seq extends mesh_base_seq;

    `uvm_object_utils(mesh_full_load_contention_seq)

    // Numero de paquetes por cada terminal fuente
    rand int unsigned num_packets_per_src;

    // Porcentaje de trafico hotspot frente a trafico disperso
    rand int unsigned hotspot_ratio; // 0 a 100

    // Numero de destinos hotspot (pocos destinos: 2 a 3)
    rand int unsigned num_hotspot_dests;

    // Constraints basicos
    constraint c_num_packets {
      num_packets_per_src inside {[5:20]};
    }

    constraint c_hotspot_ratio {
      hotspot_ratio inside {[30:70]}; // parte hotspot, parte disperso
    }

    constraint c_num_hotspot_dests {
      num_hotspot_dests inside {[2:3]}; // "pocos destinos": 2 o 3
    }

    function new(string name = "mesh_full_load_contention_seq");
      super.new(name);
    endfunction

  virtual task body();
    // ================================
    // 1) Declaraciones (SIEMPRE primero)
    // ================================
    mesh_packet tr;

    // Lista de fuentes (terminales 0..15)
    int unsigned src_terms[$];

    // Listas de destinos hotspot (pares row,col)
    bit [3:0] hotspot_rows[$];
    bit [3:0] hotspot_cols[$];

    // Índices y auxiliares
    int        s;          // índice para for de src_terms
    int        p;          // índice para paquetes por fuente
    int        i;          // índice para recorrer hotspots
    int        h;          // índice para imprimir hotspots
    int unsigned rand_pct; // valor 0..99 para decidir hotspot o disperso
    int unsigned h_idx;    // índice de hotspot elegido

    // Variables temporales para generar destinos hotspot
    bit [3:0] r_row, r_col;
    bit       found;

    // ================================
    // 2) Randomización de la secuencia
    // ================================
    if (!randomize()) begin
      `uvm_error(get_type_name(), "Fallo randomize() en mesh_full_load_contention_seq")
      return;
    end

    `uvm_info(get_type_name(),
              $sformatf("Iniciando Contencion fuerte/todos activos: num_packets_per_src=%0d hotspot_ratio=%0d num_hotspots=%0d",
                        num_packets_per_src, hotspot_ratio, num_hotspot_dests),
              UVM_MEDIUM)

    // ================================
    // 3) Construir lista de fuentes 0..15
    // ================================
    for (s = 0; s < 16; s++) begin
      src_terms.push_back(s);
    end

    // ================================
    // 4) Construir lista de destinos hotspot (2 a 3 destinos)
    //    Cada hotspot es un (row,col) válido.
    // ================================
    while (hotspot_rows.size() < num_hotspot_dests) begin
      // Elegimos un destino legal al azar
      void'(std::randomize(r_row, r_col) with {
        {r_row, r_col} inside {
          {4'd0, 4'd1}, {4'd0, 4'd2}, {4'd0, 4'd3}, {4'd0, 4'd4},
          {4'd1, 4'd0}, {4'd2, 4'd0}, {4'd3, 4'd0}, {4'd4, 4'd0},
          {4'd5, 4'd1}, {4'd5, 4'd2}, {4'd5, 4'd3}, {4'd5, 4'd4},
          {4'd1, 4'd5}, {4'd2, 4'd5}, {4'd3, 4'd5}, {4'd4, 4'd5}
        };
      });

      // Evitar hotspots duplicados
      found = 0;
      foreach (hotspot_rows[i]) begin
        if (hotspot_rows[i] == r_row && hotspot_cols[i] == r_col)
          found = 1;
      end

      if (!found) begin
        hotspot_rows.push_back(r_row);
        hotspot_cols.push_back(r_col);
      end
    end

    `uvm_info(get_type_name(),
              $sformatf("Hotspots definidos: %0d destinos", hotspot_rows.size()),
              UVM_LOW)

    foreach (hotspot_rows[h]) begin
      `uvm_info(get_type_name(),
                $sformatf("  Hotspot %0d -> row=%0d col=%0d",
                          h, hotspot_rows[h], hotspot_cols[h]),
                UVM_LOW)
    end

    // ================================
    // 5) Tráfico de carga máxima
    //    - Para cada fuente, muchos paquetes.
    //    - hotspot_ratio% va a hotspots.
    //    - El resto va a destinos dispersos legales.
    // ================================
    foreach (src_terms[s_idx]) begin
      for (p = 0; p < num_packets_per_src; p++) begin
        tr = mesh_packet::type_id::create(
          $sformatf("full_load_src%0d_pkt%0d", src_terms[s_idx], p), null);

        // Decide si este paquete es hotspot o disperso
        void'(std::randomize(rand_pct) with { rand_pct inside {[0:99]}; });

        if (rand_pct < hotspot_ratio) begin
          // -----------------------------
          // Tráfico hacia uno de los destinos hotspot
          // -----------------------------
          void'(std::randomize(h_idx) with {
            h_idx inside {[0:hotspot_rows.size()-1]};
          });

          if (!tr.randomize() with {
                src_term == src_terms[s_idx];
                dst_row  == hotspot_rows[h_idx];
                dst_col  == hotspot_cols[h_idx];
                mode     inside {MESH_MODE_ROW_FIRST, MESH_MODE_COL_FIRST};
              }) begin
            `uvm_error(get_type_name(), "Fallo randomize() en full_load hotspot")
            continue;
          end
        end
        else begin
          // -----------------------------
          // Tráfico disperso a cualquier destino legal
          // (constraints de mesh_packet ya garantizan legalidad)
          // -----------------------------
          if (!tr.randomize() with {
                src_term == src_terms[s_idx];
                mode     inside {MESH_MODE_ROW_FIRST, MESH_MODE_COL_FIRST};
              }) begin
            `uvm_error(get_type_name(), "Fallo randomize() en full_load disperso")
            continue;
          end
        end

        start_item(tr);
        finish_item(tr);

        `uvm_info(get_type_name(),
                  $sformatf("Full-load: src=%0d -> row=%0d col=%0d mode=%0d payload=0x%0h delay=%0d",
                            tr.src_term, tr.dst_row, tr.dst_col,
                            tr.mode, tr.payload, tr.delay_cycles),
                  UVM_LOW)
      end
    end

    `uvm_info(get_type_name(),
              "Finalizando Contencion fuerte/todos los puertos activos",
              UVM_MEDIUM)
  endtask


  endclass : mesh_full_load_contention_seq


  // ==================================================================
  // 11) Secuencia de caso de esquina:
  //     Arbitraje moderado hacia un mismo destino
  // ==================================================================
  //
  // Testplan:
  //   "Arbitraje moderado hacia un mismo destino"
  //
  // Objetivo:
  //   - Varias terminales (2 a 4) envian paquetes hacia un mismo destino.
  //   - Evaluar que el arbitraje es justo y no hay perdidas.
  //
  // Estrategia:
  //   - Se elige un destino fijo (row,col).
  //   - Se selecciona un conjunto reducido de fuentes (2 a 4).
  //   - Cada fuente genera un numero moderado de paquetes hacia ese destino.
  //
  class mesh_moderate_arbitration_seq extends mesh_base_seq;

    `uvm_object_utils(mesh_moderate_arbitration_seq)

    // Numero de fuentes contendiendo por el mismo destino
    rand int unsigned num_src_terms;

    // Numero de paquetes por cada fuente
    rand int unsigned num_packets_per_src;

    // Destino comun
    rand bit [3:0] target_row;
    rand bit [3:0] target_col;

    constraint c_num_src_terms_mod {
      num_src_terms inside {[2:4]};
    }

    constraint c_num_packets_mod {
      num_packets_per_src inside {[3:10]};
    }

    // Aseguramos que el destino es un External ID valido
    constraint c_target_legal {
      {target_row, target_col} inside {
        {4'd0, 4'd1}, {4'd0, 4'd2}, {4'd0, 4'd3}, {4'd0, 4'd4},
        {4'd1, 4'd0}, {4'd2, 4'd0}, {4'd3, 4'd0}, {4'd4, 4'd0},
        {4'd5, 4'd1}, {4'd5, 4'd2}, {4'd5, 4'd3}, {4'd5, 4'd4},
        {4'd1, 4'd5}, {4'd2, 4'd5}, {4'd3, 4'd5}, {4'd4, 4'd5}
      };
    }

    function new(string name = "mesh_moderate_arbitration_seq");
      super.new(name);
    endfunction

  virtual task body();
    // =================================
    // 1) Declaraciones (SIEMPRE primero)
    // =================================
    mesh_packet tr;

    // Lista de fuentes seleccionadas sin repetir
    int unsigned src_terms[$];
    int unsigned candidate;

    // Índices
    int s_idx;  // índice para foreach de src_terms
    int p;      // índice para paquetes por fuente

    // =================================
    // 2) Randomización de la secuencia
    // =================================
    if (!randomize()) begin
      `uvm_error(get_type_name(), "Fallo randomize() en mesh_moderate_arbitration_seq")
      return;
    end

    // =================================
    // 3) Selección de fuentes sin repetir
    // =================================
    //
    // Construimos src_terms con num_src_terms elementos distintos
    // escogidos aleatoriamente del rango 0..15.
    //
    while (src_terms.size() < num_src_terms) begin
      void'(std::randomize(candidate) with { candidate inside {[0:15]}; });

      if (!(candidate inside {src_terms})) begin
        src_terms.push_back(candidate);
      end
    end

    `uvm_info(get_type_name(),
              $sformatf("Arbitraje moderado: num_src_terms=%0d num_packets_per_src=%0d destino=(%0d,%0d)",
                        num_src_terms, num_packets_per_src,
                        target_row, target_col),
              UVM_MEDIUM)

    // =================================
    // 4) Generación de tráfico hacia un mismo destino
    // =================================
    //
    // Para cada fuente seleccionada:
    //   - Generamos num_packets_per_src paquetes.
    //   - Todos apuntan al mismo (target_row, target_col).
    //   - Se alterna el modo fila/columna primero de forma aleatoria.
    //
    foreach (src_terms[s_idx]) begin
      for (p = 0; p < num_packets_per_src; p++) begin
        tr = mesh_packet::type_id::create(
          $sformatf("mod_arb_src%0d_pkt%0d", src_terms[s_idx], p), null);

        if (!tr.randomize() with {
              src_term == src_terms[s_idx];
              dst_row  == target_row;
              dst_col  == target_col;
              mode     inside {MESH_MODE_ROW_FIRST, MESH_MODE_COL_FIRST};
            }) begin
          `uvm_error(get_type_name(), "Fallo randomize() en moderate_arbitration")
          continue;
        end

        start_item(tr);
        finish_item(tr);

        `uvm_info(get_type_name(),
                  $sformatf("Moderate arb: src=%0d -> row=%0d col=%0d payload=0x%0h delay=%0d",
                            tr.src_term, tr.dst_row, tr.dst_col,
                            tr.payload, tr.delay_cycles),
                  UVM_LOW)
      end
    end

    `uvm_info(get_type_name(),
              "Finalizando Arbitraje moderado hacia un mismo destino",
              UVM_MEDIUM)
  endtask


  endclass : mesh_moderate_arbitration_seq

  // ==================================================================
  // 12) Secuencia de caso de esquina:
  //     Router como terminal y destino (loopback)
  // ==================================================================
  //
  // Testplan:
  //   "Router como terminal y destino"
  //
  // Objetivo:
  //   - Validar que una terminal puede enviar un paquete que
  //     es consumido por ella misma como destino.
  //
  // Comentario:
  //   - El mapping exacto src_term -> (row,col) lo definira el
  //     environment/scoreboard. Esta secuencia genera transacciones
  //     donde el par (dst_row,dst_col) se corresponde con el mismo
  //     External Interface ID asociado a src_term segun el mapping
  //     que se programe.
  //
  // Estrategia de secuencia:
  //   - Seleccionar un conjunto de terminales origen.
  //   - Para cada una, generar paquetes donde el destino row/col
  //     se fija coherente con su propio External ID.
  //   - El scoreboard debe confirmar que src_term == dst_term.
  //
  class mesh_self_loopback_seq extends mesh_base_seq;

    `uvm_object_utils(mesh_self_loopback_seq)

    // Numero de terminales que se probaran con loopback
    rand int unsigned num_loop_terms;

    // Numero de paquetes por terminal en loopback
    rand int unsigned num_packets_per_term;

    constraint c_num_loop_terms {
      num_loop_terms inside {[1:8]};
    }

    constraint c_num_packets_loop {
      num_packets_per_term inside {[1:5]};
    }

    function new(string name = "mesh_self_loopback_seq");
      super.new(name);
    endfunction

    // Funcion helper para mapear un src_term a un (row,col) "propio".
    // Esta es una aproximacion; el mapping real puede ajustarse.
    //
    // La idea es que el environment y el scoreboard mantengan una
    // tabla consistente para que src_term y (row,col) correspondan
    // al mismo External Interface ID.
    //
    function void map_term_to_row_col(input int unsigned term,
                                      output bit [3:0] r,
                                      output bit [3:0] c);
      // Ejemplo simple:
      //   - Term 0 -> (0,1)
      //   - Term 1 -> (0,2)
      //   - Term 2 -> (0,3)
      //   - Term 3 -> (0,4)
      //   - Term 4 -> (1,0)
      //   - ...
      // Esta logica debe ajustarse para que coincida con tu figura de mapeo.
      case (term)
        0:  begin r = 4'd0; c = 4'd1; end
        1:  begin r = 4'd0; c = 4'd2; end
        2:  begin r = 4'd0; c = 4'd3; end
        3:  begin r = 4'd0; c = 4'd4; end
        4:  begin r = 4'd1; c = 4'd0; end
        5:  begin r = 4'd2; c = 4'd0; end
        6:  begin r = 4'd3; c = 4'd0; end
        7:  begin r = 4'd4; c = 4'd0; end
        8:  begin r = 4'd5; c = 4'd1; end
        9:  begin r = 4'd5; c = 4'd2; end
        10: begin r = 4'd5; c = 4'd3; end
        11: begin r = 4'd5; c = 4'd4; end
        12: begin r = 4'd1; c = 4'd5; end
        13: begin r = 4'd2; c = 4'd5; end
        14: begin r = 4'd3; c = 4'd5; end
        15: begin r = 4'd4; c = 4'd5; end
        default: begin r = 4'd0; c = 4'd1; end
      endcase
    endfunction

  virtual task body();
    // =================================
    // 1) Declaraciones (SIEMPRE primero)
    // =================================
    mesh_packet tr;

    // Terminales que se probarán en loopback
    int unsigned loop_terms[$];
    int unsigned candidate;

    // Índices y variables auxiliares
    int idx;           // índice para foreach(loop_terms[idx])
    int p;             // índice para paquetes por terminal
    bit [3:0] r, c;    // fila y columna asociadas al terminal

    // =================================
    // 2) Randomización de la secuencia
    // =================================
    if (!randomize()) begin
      `uvm_error(get_type_name(), "Fallo randomize() en mesh_self_loopback_seq")
      return;
    end

    // =================================
    // 3) Selección de terminales en loopback
    // =================================
    //
    // Construir loop_terms con num_loop_terms terminales
    // distintos escogidos aleatoriamente en 0..15.
    //
    while (loop_terms.size() < num_loop_terms) begin
      void'(std::randomize(candidate) with { candidate inside {[0:15]}; });
      if (!(candidate inside {loop_terms})) begin
        loop_terms.push_back(candidate);
      end
    end

    `uvm_info(get_type_name(),
              $sformatf("Router como terminal y destino: num_loop_terms=%0d num_packets_per_term=%0d",
                        num_loop_terms, num_packets_per_term),
              UVM_MEDIUM)

    // =================================
    // 4) Generación de tráfico loopback
    // =================================
    //
    // Para cada terminal seleccionado:
    //   - Lo mapeamos a (row,col) con map_term_to_row_col()
    //   - Generamos num_packets_per_term paquetes
    //   - src_term y destino (row,col) son coherentes con ese terminal
    //
    foreach (loop_terms[idx]) begin
      // Obtener coordenadas asociadas al terminal
      map_term_to_row_col(loop_terms[idx], r, c);

      for (p = 0; p < num_packets_per_term; p++) begin
        tr = mesh_packet::type_id::create(
          $sformatf("loopback_term%0d_pkt%0d", loop_terms[idx], p), null);

        if (!tr.randomize() with {
              src_term == loop_terms[idx];
              dst_row  == r;
              dst_col  == c;
              mode     inside {MESH_MODE_ROW_FIRST, MESH_MODE_COL_FIRST};
            }) begin
          `uvm_error(get_type_name(), "Fallo randomize() en self_loopback")
          continue;
        end

        start_item(tr);
        finish_item(tr);

        `uvm_info(get_type_name(),
                  $sformatf("Loopback: term=%0d -> row=%0d col=%0d payload=0x%0h delay=%0d",
                            tr.src_term, tr.dst_row, tr.dst_col,
                            tr.payload, tr.delay_cycles),
                  UVM_LOW)
      end
    end

    `uvm_info(get_type_name(),
              "Finalizando Router como terminal y destino",
              UVM_MEDIUM)
  endtask


  endclass : mesh_self_loopback_seq



// Dentro de package mesh_uvm_pkg;

  // ------------------------------------------------------------
  // Evento de salida hacia el scoreboard: mesh_out_event
  //
  // Representa un paquete que el DUT ha entregado a una terminal.
  // Se usa como tipo en:
  //   - mesh_sink_monitor.ap (analysis_port)
  //   - mesh_scoreboard (analysis_imp de salida)
  // ------------------------------------------------------------
  class mesh_out_event extends uvm_object;

    `uvm_object_utils(mesh_out_event)

    // Terminal destino (0..15) donde se hizo pop
    int unsigned dst_term;

    // Campos decodificados del vector de 40 bits
    bit [7:0]   nxt_jump;
    bit [3:0]   dst_row;
    bit [3:0]   dst_col;
    mesh_mode_e mode;
    bit [22:0]  payload;

    // Vector completo tal como lo entrega el DUT
    bit [39:0]  data;

    // Tiempo de recepción (cuando se hizo pop)
    time recv_time;

    function new(string name = "mesh_out_event");
      super.new(name);
    endfunction

  endclass : mesh_out_event



//////////////////////////////////////////////////////////////////////////
//////////////////////////Agente_entrada//////////////////////////////////

// ===============================================================
// Sequencer de entrada: mesh_sequencer
// - Tipo de item: mesh_packet
// - Recibe las secuencias (conectividad aleatoria, modos, broadcast, etc)
//   y entrega los mesh_packet al driver.
// ===============================================================

class mesh_sequencer extends uvm_sequencer #(mesh_packet);

  `uvm_component_utils(mesh_sequencer)

  function new(string name = "mesh_sequencer", uvm_component parent = null);
    super.new(name, parent);
  endfunction

endclass : mesh_sequencer


// ===============================================================
// Driver de entrada: mesh_driver
//
// Responsabilidades:
//   - Toma mesh_packet del sequencer.
//   - Convierte la transacción al paquete de 40 bits.
//   - Maneja el handshake con el DUT via pndng_i_in / popin.
//   - Registra send_time en la transacción cuando el DUT acepta
//     el paquete (popin).
//
// Nota: se apoya en un virtual interface mesh_if que debes
//       conectar desde el test o el env.
// ===============================================================

//typedef virtual mesh_if mesh_vif_t;  // Ajusta el nombre 

class mesh_driver extends uvm_driver #(mesh_packet);

  `uvm_component_utils(mesh_driver)

  // Virtual interface hacia el DUT
  mesh_vif_t vif;

  // Número fijo de terminales (según tu testplan 16)
  localparam int NTERMS = 16;

  function new(string name = "mesh_driver", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  // Obtener el virtual interface desde la config DB
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(mesh_vif_t)::get(this, "", "vif", vif)) begin
      `uvm_fatal(get_type_name(),
                 "No se pudo obtener el virtual interface 'vif' para mesh_driver")
    end
  endfunction

  // Bucle principal del driver
  virtual task run_phase(uvm_phase phase);
    mesh_packet tr;
    bit [39:0] pkt_bits;
    int unsigned s;

    // Se asegura de que las señales de entrada empiecen limpias
    // (esto se puede hacer también en el testbench fuera de UVM)
    for (s = 0; s < NTERMS; s++) begin
      vif.pndng_i_in[s]    <= 1'b0;
      vif.data_out_i_in[s] <= '0;
    end

    forever begin
      // Espera una transacción de secuencia
      seq_item_port.get_next_item(tr);

      s = tr.src_term;
      if (s >= NTERMS) begin
        `uvm_error(get_type_name(),
                   $sformatf("src_term=%0d fuera de rango (NTERMS=%0d)", s, NTERMS))
        seq_item_port.item_done();
        continue;
      end

      // Construir el paquete de 40 bits a partir de la transacción
      pkt_bits = tr.to_bits();

      // Esperar delay_cycles antes de enviar (según testplan)
      repeat (tr.delay_cycles) @(posedge vif.clk);

      `uvm_info(get_type_name(),
                $sformatf("Driver: enviando paquete desde src_term=%0d bits=%h delay=%0d",
                          s, pkt_bits, tr.delay_cycles),
                UVM_LOW)

      // Colocar el dato y poner pendiente
      @(posedge vif.clk);
      vif.data_out_i_in[s] <= pkt_bits;
      vif.pndng_i_in[s]    <= 1'b1;

      // Esperar a que el DUT haga popin en esa terminal
      // Esto indica que la FIFO de entrada consumió el paquete.
      @(posedge vif.clk);
      wait (vif.popin[s] == 1'b1);

      // Momento en que el DUT acepta el paquete
      tr.send_time = $time;

      `uvm_info(get_type_name(),
                $sformatf("Driver: DUT hizo popin en src_term=%0d tiempo=%0t", s, tr.send_time),
                UVM_LOW)

      // En el siguiente ciclo bajamos el pendiente y limpiamos el dato
      @(posedge vif.clk);
      vif.pndng_i_in[s]    <= 1'b0;
      vif.data_out_i_in[s] <= '0;

      // Informar al sequencer que terminamos con este item
      seq_item_port.item_done();
    end
  endtask

endclass : mesh_driver


// ===============================================================
// Monitor de entrada: mesh_src_monitor
//
// Responsabilidades:
//   - Observar las señales de entrada del DUT:
//       * pndng_i_in[0..15]
//       * popin[0..15]
//       * data_out_i_in[0..15]
//   - Detectar el momento exacto en que el DUT acepta un paquete
//     (popin[t] activo) para alguna terminal.
//   - Construir una transacción mesh_packet que contenga:
//       * src_term
//       * dst_row, dst_col, mode, payload (decodificados del vector)
//       * send_time = tiempo de aceptación
//   - Enviarla al scoreboard via un analysis_port.
// ===============================================================

class mesh_src_monitor extends uvm_component;

  `uvm_component_utils(mesh_src_monitor)

  // Virtual interface hacia el DUT
  mesh_vif_t vif;

  // Analysis port hacia el scoreboard
  uvm_analysis_port #(mesh_packet) ap;

  // Número de terminales
  localparam int NTERMS = 16;

  // Registro del valor anterior de popin para detectar flancos
  bit prev_popin[NTERMS];

  function new(string name = "mesh_src_monitor", uvm_component parent = null);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction

  // Obtener el virtual interface
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(mesh_vif_t)::get(this, "", "vif", vif)) begin
      `uvm_fatal(get_type_name(),
                 "No se pudo obtener el virtual interface 'vif' para mesh_src_monitor")
    end
  endfunction

  virtual task run_phase(uvm_phase phase);
    bit [39:0] pkt_bits;
    mesh_packet tr;

    // Inicializar prev_popin
    for (int t = 0; t < NTERMS; t++) begin
      prev_popin[t] = 1'b0;
    end

    forever begin
      @(posedge vif.clk);
      if (vif.reset) begin
        // Mientras reset, limpiamos el historial de popin
        for (int t = 0; t < NTERMS; t++) begin
          prev_popin[t] = 1'b0;
        end
      end
      else begin
        // Recorremos todas las terminales para ver si hay evento de popin
        for (int t = 0; t < NTERMS; t++) begin
          // Detectar flanco ascendente de popin o popin activo
          if ((vif.popin[t] == 1'b1) && (prev_popin[t] == 1'b0)) begin

            // Capturamos el paquete que el DUT esta consumiendo
            pkt_bits = vif.data_out_i_in[t];

            tr = mesh_packet::type_id::create(
                   $sformatf("src_mon_tr_term%0d_time%0t", t, $time), this);

            tr.src_term  = t;
            tr.send_time = $time;

            // Decodificacion de campos segun tu testplan:
            // [39:32] Nxt jump     (lo escribe el DUT, aqui lo dejamos como llega)
            // [31:28] Row
            // [27:24] Column
            // [23]    Mode (mapeo simple a enum)
            // [22:0]  Payload
            tr.nxt_jump = pkt_bits[39:32];
            tr.dst_row  = pkt_bits[31:28];
            tr.dst_col  = pkt_bits[27:24];

            // Mapeo simple del bit Mode a enum:
            //   bit = 1 -> MESH_MODE_ROW_FIRST
            //   bit = 0 -> MESH_MODE_COL_FIRST
            // Para broadcast se puede trabajar con otro criterio si lo deseas.
            if (pkt_bits[23] == 1'b1)
              tr.mode = MESH_MODE_ROW_FIRST;
            else
              tr.mode = MESH_MODE_COL_FIRST;

            tr.payload = pkt_bits[22:0];

            `uvm_info(get_type_name(),
                      $sformatf("Monitor SRC: popin en term=%0d tiempo=%0t bits=%h row=%0d col=%0d mode=%0d payload=0x%0h",
                                t, tr.send_time, pkt_bits,
                                tr.dst_row, tr.dst_col, tr.mode, tr.payload),
                      UVM_LOW)

            // Enviamos la transacción al scoreboard
            ap.write(tr);
          end

          // Actualizar historial de popin
          prev_popin[t] = vif.popin[t];
        end
      end
    end
  endtask

endclass : mesh_src_monitor


// ===============================================================
// Agente de entrada: mesh_src_agent
//
// Componentes internos:
//   - mesh_sequencer  (sequencer de transacciones mesh_packet)
//   - mesh_driver     (driver que inyecta paquetes en pndng_i_in/data_out_i_in)
//   - mesh_src_monitor (monitor que observa popin y captura eventos de entrada)
//
// El agente recibe un virtual interface 'vif' via config DB y
// lo pasa al driver y al monitor.
// ===============================================================

class mesh_src_agent extends uvm_agent;

  `uvm_component_utils(mesh_src_agent)

  // Virtual interface hacia el DUT
  mesh_vif_t vif;

  // Componentes internos
  mesh_sequencer    seqr;
  mesh_driver       drv;
  mesh_src_monitor  mon;

  function new(string name = "mesh_src_agent", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Obtener el virtual interface para el agente
    if (!uvm_config_db#(mesh_vif_t)::get(this, "", "vif", vif)) begin
      `uvm_fatal(get_type_name(),
                 "No se pudo obtener el virtual interface 'vif' para mesh_src_agent")
    end

    // Crear componentes
    seqr = mesh_sequencer   ::type_id::create("seqr", this);
    drv  = mesh_driver      ::type_id::create("drv",  this);
    mon  = mesh_src_monitor ::type_id::create("mon",  this);

    // Propagar el virtual interface a driver y monitor
    uvm_config_db#(mesh_vif_t)::set(this, "drv", "vif", vif);
    uvm_config_db#(mesh_vif_t)::set(this, "mon", "vif", vif);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    // Conectar sequencer con driver
    drv.seq_item_port.connect(seqr.seq_item_export);
  endfunction

endclass : mesh_src_agent



// ===============================================================
// Sink driver de salida: mesh_sink_driver
//
// Responsabilidades:
//   - Observar pndng[0..15] en todas las terminales.
//   - Para pruebas normales: cuando pndng[t] == 1 y el puerto está
//     habilitado, hacer pop[t] = 1 para consumir el dato.
//   - Para la prueba "FIFO llena y back-pressure": se puede desactivar
//     el auto-pop global o por puerto usando una máscara.
//
// Configuración:
//   - enable_auto_pop: si es 1, el driver intentará drenar las FIFOs.
//   - pop_enable_mask[t]: si es 1, ese terminal se puede drenar;
//                         si es 0, nunca se hace pop en ese terminal.
//   Ambas variables se pueden ajustar por uvm_config_db.
// ===============================================================

class mesh_sink_driver extends uvm_component;

  `uvm_component_utils(mesh_sink_driver)

  mesh_vif_t vif;

  // Número de terminales
  localparam int NTERMS = 16;

  // Configuración de comportamiento
  bit enable_auto_pop = 1'b1;               // por defecto drenamos todo
  bit [NTERMS-1:0] pop_enable_mask = '1;    // por defecto todos los puertos

  function new(string name = "mesh_sink_driver", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(mesh_vif_t)::get(this, "", "vif", vif)) begin
      `uvm_fatal(get_type_name(),
                 "No se pudo obtener el virtual interface 'vif' para mesh_sink_driver")
    end

    // Permitir que el test configure enable_auto_pop y pop_enable_mask
    void'(uvm_config_db#(bit)::get(this, "", "enable_auto_pop", enable_auto_pop));
    void'(uvm_config_db#(bit [NTERMS-1:0])::get(
            this, "", "pop_enable_mask", pop_enable_mask));
  endfunction

  virtual task run_phase(uvm_phase phase);
    // Inicializamos pop en 0
    for (int t = 0; t < NTERMS; t++) begin
      vif.pop[t] <= 1'b0;
    end

    forever begin
      @(posedge vif.clk);

      if (vif.reset) begin
        // En reset, pop en 0 para todos
        for (int t = 0; t < NTERMS; t++) begin
          vif.pop[t] <= 1'b0;
        end
      end
      else begin
        // Si auto-pop está desactivado, mantenemos pop en 0 y no drenamos
        if (!enable_auto_pop) begin
          for (int t = 0; t < NTERMS; t++) begin
            vif.pop[t] <= 1'b0;
          end
        end
        else begin
          // Modo automático: si hay pndng y el puerto está habilitado,
          // hacemos pop=1 (se puede mantener en 1 mientras pndng=1).
          for (int t = 0; t < NTERMS; t++) begin
            if (pop_enable_mask[t] && vif.pndng[t]) begin
              vif.pop[t] <= 1'b1;
            end
            else begin
              vif.pop[t] <= 1'b0;
            end
          end
        end
      end
    end
  endtask

endclass : mesh_sink_driver


// ===============================================================
// Monitor de salida: mesh_sink_monitor
//
// Responsabilidades:
//   - Observar:
//       * pndng[0..15]
//       * pop[0..15]
//       * data_out[0..15]
//   - Cuando para una terminal t se cumple pndng[t]==1 y pop[t]==1
//     en un ciclo de reloj, asume que se está extrayendo un paquete.
//   - Toma:
//       * dst_term = t
//       * data_out[t] (40 bits)
//       * recv_time = $time
//     Decodifica nxt_jump, row, col, mode, payload y los empaqueta
//     en un mesh_out_event que envía al scoreboard por ap.
// ===============================================================

class mesh_sink_monitor extends uvm_component;

  `uvm_component_utils(mesh_sink_monitor)

  mesh_vif_t vif;

  // Analysis port hacia el scoreboard
  uvm_analysis_port #(mesh_out_event) ap;

  localparam int NTERMS = 16;

  function new(string name = "mesh_sink_monitor", uvm_component parent = null);
    super.new(name, parent);
    ap = new("ap", this);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(mesh_vif_t)::get(this, "", "vif", vif)) begin
      `uvm_fatal(get_type_name(),
                 "No se pudo obtener el virtual interface 'vif' para mesh_sink_monitor")
    end
  endfunction

  virtual task run_phase(uvm_phase phase);
    bit [39:0] bits;
    mesh_out_event evt;

    forever begin
      @(posedge vif.clk);

      if (vif.reset) begin
        // En reset no hacemos nada, solo esperamos salir de reset
      end
      else begin
        for (int t = 0; t < NTERMS; t++) begin
          // Criterio de observación:
          //   - pndng[t] == 1 (hay dato disponible)
          //   - pop[t] == 1 (el entorno está extrayendo ese dato)
          if (vif.pndng[t] && vif.pop[t]) begin
            bits = vif.data_out[t];

            evt = mesh_out_event::type_id::create(
                    $sformatf("out_evt_term%0d_time%0t", t, $time), this);

            evt.dst_term  = t;
            evt.recv_time = $time;

            // Decodificar campos según tu formato:
            // [39:32] Nxt jump
            // [31:28] Row
            // [27:24] Column
            // [23]    Mode (bit que se mapea a un enum)
            // [22:0]  Payload
            
            // guardar el vector completo
            evt.data      = bits;
            
            evt.nxt_jump = bits[39:32];
            evt.dst_row  = bits[31:28];
            evt.dst_col  = bits[27:24];
            evt.payload  = bits[22:0];

            // Mapeo simple Mode -> enum mesh_mode_e
            if (bits[23] == 1'b1)
              evt.mode = MESH_MODE_ROW_FIRST;
            else
              evt.mode = MESH_MODE_COL_FIRST;
            // Si quieres soportar broadcast en la salida, se puede
            // agregar una convención extra sobre algún campo.

            `uvm_info(get_type_name(),
                      $sformatf("Monitor SINK: dst_term=%0d time=%0t bits=%h row=%0d col=%0d mode=%0d payload=0x%0h",
                                evt.dst_term, evt.recv_time, bits,
                                evt.dst_row, evt.dst_col, evt.mode, evt.payload),
                      UVM_LOW)

            // Enviamos el evento al scoreboard
            ap.write(evt);
          end
        end
      end
    end
  endtask

endclass : mesh_sink_monitor


// ===============================================================
// Agente de salida: mesh_sink_agent
//
// Componentes internos:
//   - mesh_sink_driver  (drv)  -> genera pop[] para consumir datos
//   - mesh_sink_monitor (mon)  -> observa pndng/pops/data_out y
//                                 envía eventos al scoreboard
//
// El agente recibe un virtual interface 'vif' via config DB y
// lo distribuye a sus subcomponentes.
// ===============================================================

class mesh_sink_agent extends uvm_agent;

  `uvm_component_utils(mesh_sink_agent)

  mesh_vif_t vif;

  mesh_sink_driver  drv;
  mesh_sink_monitor mon;

  function new(string name = "mesh_sink_agent", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(mesh_vif_t)::get(this, "", "vif", vif)) begin
      `uvm_fatal(get_type_name(),
                 "No se pudo obtener el virtual interface 'vif' para mesh_sink_agent")
    end

    drv = mesh_sink_driver ::type_id::create("drv", this);
    mon = mesh_sink_monitor::type_id::create("mon", this);

    // Propagar el virtual interface a los subcomponentes
    uvm_config_db#(mesh_vif_t)::set(this, "drv", "vif", vif);
    uvm_config_db#(mesh_vif_t)::set(this, "mon", "vif", vif);
  endfunction

endclass : mesh_sink_agent



endpackage : mesh_uvm_pkg

//////////////////////////////////////////////////////////////////////////
//////////////////////////Interfase///////////////////////////////////////

// mesh_if.sv
//
// Interface para conectar la malla 4x4 con el ambiente UVM.
// Refleja las mismas señales que tu testbench "manual".

interface mesh_if #(
  parameter int ROWS   = 4,
  parameter int COLUMS = 4,
  parameter int PCK_W  = 40
);

  // Numero de terminales externas
  localparam int NTERMS = ROWS*2 + COLUMS*2;

  // Reloj y reset
  logic clk;
  logic reset;

  // Señales desde el DUT hacia el exterior
  logic                  pndng      [NTERMS];      // hay dato para la terminal
  logic [PCK_W-1:0]      data_out   [NTERMS];      // datos saliendo de la malla
  logic                  popin      [NTERMS];      // DUT consumiendo del exterior

  // Señales desde el exterior (TB/UVM) hacia el DUT
  logic                  pop        [NTERMS];      // exterior hace pop a la malla
  logic [PCK_W-1:0]      data_out_i_in[NTERMS];    // datos inyectados a la malla
  logic                  pndng_i_in [NTERMS];      // hay paquete disponible para el DUT

  // Modport para conectar el DUT
  //
  // Desde la perspectiva del DUT:
  //   - Recibe clk, reset, pop, data_out_i_in, pndng_i_in
  //   - Entrega pndng, data_out, popin
  //
  modport dut (
    input  clk,
    input  reset,
    input  pop,
    input  data_out_i_in,
    input  pndng_i_in,
    output pndng,
    output data_out,
    output popin
  );

  // Modport para el testbench UVM (driver y monitores)
  //
  // Desde la perspectiva del TB:
  //   - Observa clk, reset, pndng, data_out, popin
  //   - Maneja pop, data_out_i_in, pndng_i_in
  //
  modport tb (
    input  clk,
    input  reset,
    input  pndng,
    input  data_out,
    input  popin,
    output pop,
    output data_out_i_in,
    output pndng_i_in
  );

endinterface : mesh_if



package mesh_scoreboard_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
 import mesh_uvm_pkg::*; // mesh_packet, mesh_out_event, mesh_mode_e, etc.

  // ================================================================
  // 1) Clase helper: mesh_expected_pkt
  // ================================================================
  class mesh_expected_pkt extends uvm_object;

    `uvm_object_utils(mesh_expected_pkt)

    int unsigned src_term;
    bit [3:0]    dst_row;
    bit [3:0]    dst_col;
    mesh_mode_e  mode;
    bit [22:0]   payload;

    bit [7:0]    nxt_jump;
    bit [39:0]   full_bits;

    time         send_time;

    function new(string name = "mesh_expected_pkt");
      super.new(name);
    endfunction

  endclass : mesh_expected_pkt

  // ================================================================
  // 2) Reference model: mesh_ref_model
  // ================================================================
  class mesh_ref_model extends uvm_object;

    `uvm_object_utils(mesh_ref_model)

    protected mesh_expected_pkt expected_q[$];

    function new(string name = "mesh_ref_model");
      super.new(name);
    endfunction

    // Tabla nxt_jump según dst_row/dst_col
    function automatic bit [7:0] calc_nxt_jump(bit [3:0] dst_row,
                                               bit [3:0] dst_col);
      bit [7:0] val;

      // Norte
      if (dst_row == 4'd0 && dst_col inside {4'd1,4'd2,4'd3,4'd4})
        val = 8'd0;
      // Oeste
      else if (dst_col == 4'd0 && dst_row inside {4'd1,4'd2,4'd3,4'd4})
        val = 8'd3;
      // Sur
      else if (dst_row == 4'd5 && dst_col inside {4'd1,4'd2,4'd3,4'd4})
        val = 8'd2;
      // Este
      else if (dst_col == 4'd5 && dst_row inside {4'd1,4'd2,4'd3,4'd4})
        val = 8'd1;
      else
        val = 8'hFF; // no mapeado

      return val;
    endfunction

    function automatic bit [39:0] build_full_bits(bit [7:0]   nxt_jump,
                                                  bit [3:0]   dst_row,
                                                  bit [3:0]   dst_col,
                                                  mesh_mode_e mode,
                                                  bit [22:0]  payload);
      bit [39:0] pkt;
      bit        mode_bit;

      case (mode)
        MESH_MODE_ROW_FIRST: mode_bit = 1'b1;
        MESH_MODE_COL_FIRST: mode_bit = 1'b0;
        MESH_MODE_BCAST:     mode_bit = 1'b1;
        default:             mode_bit = 1'b0;
      endcase

      pkt = '0;
      pkt[39:32] = nxt_jump;
      pkt[31:28] = dst_row;
      pkt[27:24] = dst_col;
      pkt[23]    = mode_bit;
      pkt[22:0]  = payload;
      return pkt;
    endfunction

    // Entrada del modelo: mesh_packet desde el monitor de entrada
    virtual function void add_input_tr(mesh_packet in_tr);
      mesh_expected_pkt exp;
      bit [7:0]  loc_nxt;
      bit [39:0] loc_bits;

      loc_nxt  = calc_nxt_jump(in_tr.dst_row, in_tr.dst_col);
      loc_bits = build_full_bits(loc_nxt,
                                 in_tr.dst_row,
                                 in_tr.dst_col,
                                 in_tr.mode,
                                 in_tr.payload);

      exp = mesh_expected_pkt::type_id::create("exp_pkt");
      exp.src_term  = in_tr.src_term;
      exp.dst_row   = in_tr.dst_row;
      exp.dst_col   = in_tr.dst_col;
      exp.mode      = in_tr.mode;
      exp.payload   = in_tr.payload;
      exp.nxt_jump  = loc_nxt;
      exp.full_bits = loc_bits;
      exp.send_time = in_tr.send_time;

      expected_q.push_back(exp);

      `uvm_info(get_type_name(),
                $sformatf("REF: agregado esperado full_bits=%h src_term=%0d row=%0d col=%0d mode=%0d payload=0x%0h nxt=0x%0h",
                          exp.full_bits, exp.src_term, exp.dst_row,
                          exp.dst_col, exp.mode, exp.payload, exp.nxt_jump),
                UVM_LOW)
    endfunction

    // Intentar hacer match con una salida
    virtual function bit match_output_ev(mesh_out_event out_ev,
                                         output mesh_expected_pkt matched);
      bit        found = 0;
      bit [39:0] out_bits;

      out_bits = out_ev.data;

      for (int i = 0; i < expected_q.size(); i++) begin
        if (expected_q[i].full_bits === out_bits) begin
          matched = expected_q[i];
          expected_q.delete(i);
          found = 1;
          break;
        end
      end

      if (found)
        `uvm_info(get_type_name(),
                  $sformatf("REF: match encontrado para data=%h", out_bits),
                  UVM_LOW)
      else
        `uvm_warning(get_type_name(),
                     $sformatf("REF: no hay match para data=%h", out_bits))

      return found;
    endfunction

    virtual function int unsigned num_pending();
      return expected_q.size();
    endfunction

    virtual function void report_pending();
      if (expected_q.size() == 0) begin
        `uvm_info(get_type_name(), "REF: sin pendientes", UVM_LOW)
        return;
      end

      `uvm_error(get_type_name(),
                 $sformatf("REF: quedan %0d paquetes esperados sin match",
                           expected_q.size()))

      foreach (expected_q[i]) begin
        `uvm_info(get_type_name(),
                  $sformatf("Pendiente[%0d]: full_bits=%h src=%0d row=%0d col=%0d mode=%0d payload=0x%0h nxt=0x%0h",
                            i,
                            expected_q[i].full_bits,
                            expected_q[i].src_term,
                            expected_q[i].dst_row,
                            expected_q[i].dst_col,
                            expected_q[i].mode,
                            expected_q[i].payload,
                            expected_q[i].nxt_jump),
                  UVM_LOW)
      end
    endfunction

  endclass : mesh_ref_model

  // ================================================================
  // 3) Scoreboard: mesh_scoreboard
  // ================================================================

// Declarar dos analysis_imp con nombres distintos
`uvm_analysis_imp_decl(_in)
`uvm_analysis_imp_decl(_out)

  class mesh_scoreboard extends uvm_component;

    `uvm_component_utils(mesh_scoreboard)

    mesh_ref_model refm;

    // Entrada: desde mesh_src_monitor (mesh_packet)
    uvm_analysis_imp_in #(mesh_packet,    mesh_scoreboard) in_imp;

    // Salida: desde mesh_sink_monitor (mesh_out_event)
    uvm_analysis_imp_out #(mesh_out_event, mesh_scoreboard) out_imp;

    int unsigned num_matches;
    int unsigned num_mismatches;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      refm  = mesh_ref_model::type_id::create("refm");
      in_imp  = new("in_imp",  this);
      out_imp = new("out_imp", this);

      num_matches    = 0;
      num_mismatches = 0;
    endfunction

    // write() para mesh_packet (entrada)
    virtual function void write_in(mesh_packet tr);
      `uvm_info(get_type_name(),
                $sformatf("SCB: evento entrada src=%0d row=%0d col=%0d mode=%0d payload=0x%0h t=%0t",
                          tr.src_term, tr.dst_row, tr.dst_col, tr.mode,
                          tr.payload, tr.send_time),
                UVM_LOW)
      refm.add_input_tr(tr);
    endfunction

    // write() para mesh_out_event (salida)
    virtual function void write_out(mesh_out_event ev);
      mesh_expected_pkt exp;
      bit ok;
      time delay;

      `uvm_info(get_type_name(),
                $sformatf("SCB: evento salida dst_term=%0d data=%h t=%0t",
                          ev.dst_term, ev.data, ev.recv_time),
                UVM_LOW)

      ok = refm.match_output_ev(ev, exp);

      if (ok) begin
        num_matches++;
        delay = ev.recv_time - exp.send_time;

        `uvm_info(get_type_name(),
                  $sformatf("SCB: MATCH OK src=%0d -> dst_row=%0d,dst_col=%0d delay=%0t data=%h",
                            exp.src_term, exp.dst_row, exp.dst_col,
                            delay, ev.data),
                  UVM_MEDIUM)
      end
      else begin
        num_mismatches++;
        `uvm_error(get_type_name(),
                   $sformatf("SCB: NO MATCH para data=%h en dst_term=%0d t=%0t",
                             ev.data, ev.dst_term, ev.recv_time))
      end
    endfunction

    virtual function void final_phase(uvm_phase phase);
      super.final_phase(phase);

      `uvm_info(get_type_name(),
                $sformatf("SCB final: matches=%0d mismatches=%0d",
                          num_matches, num_mismatches),
                UVM_LOW)

      if (refm.num_pending() != 0)
        refm.report_pending();
    endfunction

  endclass : mesh_scoreboard



// mesh_env_pkg.sv
//
// Paquete que define el ambiente UVM para la malla 4x4.
//
// Contiene:
//   - Clase mesh_env:
//       * Instancia:
//           - mesh_src_agent   (agente de entrada)
//           - mesh_sink_agent  (agente de salida)
//           - mesh_scoreboard  (scoreboard + reference model)
//       * Conecta los analysis_ports de los monitores hacia el scoreboard.
//
// Requisitos externos:
//   - package mesh_uvm_pkg        (mesh_packet, mesh_out_event, secuencias, etc.)
//   - package mesh_agent_pkg      (mesh_src_agent, mesh_sink_agent, drivers/monitores)
//   - package mesh_scoreboard_pkg (mesh_scoreboard, mesh_ref_model, etc.)
//   - interface mesh_vif          (con señales pndng, pop, pndng_i_in, popin, data_out, etc.)
//


class mesh_env extends uvm_env;

  `uvm_component_utils(mesh_env)

  // Agente de entrada (inyecta paquetes al DUT)
  mesh_src_agent   src_agent;

  // Agente de salida (extrae paquetes del DUT)
  mesh_sink_agent  sink_agent;

  // Scoreboard (incluye el reference model)
  mesh_scoreboard  scb;

  // ------------------------------------------
  // Constructor
  // ------------------------------------------
  function new(string name = "mesh_env", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  // ------------------------------------------
  // build_phase:
  //   - Crear los subcomponentes usando el factory.
  // ------------------------------------------
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Crear agente de entrada
    src_agent  = mesh_src_agent ::type_id::create("src_agent",  this);

    // Crear agente de salida
    sink_agent = mesh_sink_agent::type_id::create("sink_agent", this);

    // Crear scoreboard
    scb        = mesh_scoreboard::type_id::create("scb",        this);

    `uvm_info(get_type_name(),
              "mesh_env: build_phase completado (src_agent, sink_agent, scb creados)",
              UVM_LOW)
  endfunction

  // ------------------------------------------
  // connect_phase:
  //   - Conectar los analysis_ports de los monitores
  //     hacia los analysis_imp del scoreboard.
  // ------------------------------------------
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    // Monitor de entrada -> scoreboard
    src_agent.mon.ap.connect(scb.in_imp);

    // Monitor de salida  -> scoreboard
    sink_agent.mon.ap.connect(scb.out_imp);

    `uvm_info(get_type_name(),
              "mesh_env: connect_phase completado (monitores conectados al scoreboard)",
              UVM_LOW)
  endfunction

endclass : mesh_env

endpackage : mesh_scoreboard_pkg





// mesh_test_pkg.sv
//
// Package con las clases de test UVM para la malla 4x4.
//
// Supone que ya existe mesh_uvm_pkg con:
//   - mesh_packet, secuencias (rand_connectivity, compare_modes, broadcast, corner cases)
//   - agentes (mesh_src_agent, mesh_sink_agent)
//   - scoreboard (mesh_scoreboard)
//   - ambiente (mesh_env)
//   - typedef virtual mesh_if.tb mesh_vif_t;

package mesh_test_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import mesh_uvm_pkg::*;  // trae env, seqs, scoreboard, etc.
  import mesh_scoreboard_pkg::*;

  // ============================================================
  // 1) Test base: mesh_base_test
  //
  // Responsabilidades:
  //   - Crear el ambiente mesh_env.
  //   - Proveer un handle env para los tests derivados.
  //   - NO lanza secuencias por sí mismo.
  // ============================================================

  

  class mesh_base_test extends uvm_test;

    `uvm_component_utils(mesh_base_test)

    // Ambiente principal
    mesh_env env;

    function new(string name = "mesh_base_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      // Crear el ambiente
      env = mesh_env::type_id::create("env", this);
    endfunction

    virtual task run_phase(uvm_phase phase);
      // El test base no hace nada aqui, los derivados
      // son los que arrancan secuencias en el sequencer.
      `uvm_info(get_type_name(),
                "mesh_base_test: run_phase vacio (usar clases derivadas)",
                UVM_LOW)
    endtask

  endclass : mesh_base_test

  // ============================================================
  // 2) Test: Conectividad aleatoria
  //
  // Lanza la secuencia mesh_rand_connectivity_seq sobre el
  // sequencer del agente de entrada (src_agent).
  // ============================================================

  class mesh_rand_connectivity_test extends mesh_base_test;

    `uvm_component_utils(mesh_rand_connectivity_test)

    function new(string name = "mesh_rand_connectivity_test",
                 uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
      mesh_rand_connectivity_seq seq;

      phase.raise_objection(this, "Iniciando Conectividad aleatoria");

      // Crear la secuencia
      seq = mesh_rand_connectivity_seq::type_id::create("seq", this);

      // Arrancar la secuencia sobre el sequencer del agente de origen
      // (nombre asumido: env.src_agt.seqr)
      seq.start(env.src_agent.seqr);

      // Pequeña espera extra para que drene todo
      #(1000ns);

      phase.drop_objection(this, "Finalizando Conectividad aleatoria");
    endtask

  endclass : mesh_rand_connectivity_test

  // ============================================================
  // 3) Test: Comparacion de modos de ruta
  //
  // Lanza mesh_compare_modes_seq.
  // Se espera que el scoreboard mida latencias, hops, etc.
  // ============================================================

  class mesh_compare_modes_test extends mesh_base_test;

    `uvm_component_utils(mesh_compare_modes_test)

    function new(string name = "mesh_compare_modes_test",
                 uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
      mesh_compare_modes_seq seq;

      phase.raise_objection(this, "Iniciando Comparacion de modos de ruta");

      seq = mesh_compare_modes_seq::type_id::create("seq", this);
      seq.start(env.src_agent.seqr);

      #(1000ns);

      phase.drop_objection(this, "Finalizando Comparacion de modos de ruta");
    endtask

  endclass : mesh_compare_modes_test

  // ============================================================
  // 4) Test: Broadcast funcional
  //
  // Lanza mesh_broadcast_seq.
  // El scoreboard debe verificar que todas las terminales
  // (menos el origen) reciben el mismo payload.
  // ============================================================

  class mesh_broadcast_test extends mesh_base_test;

    `uvm_component_utils(mesh_broadcast_test)

    function new(string name = "mesh_broadcast_test",
                 uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
      mesh_broadcast_seq seq;

      phase.raise_objection(this, "Iniciando Broadcast funcional");

      seq = mesh_broadcast_seq::type_id::create("seq", this);
      seq.start(env.src_agent.seqr);

      #(1000ns);

      phase.drop_objection(this, "Finalizando Broadcast funcional");
    endtask

  endclass : mesh_broadcast_test

  // ============================================================
  // 5) Tests de casos de esquina
  //
  // Cada uno simplemente lanza la secuencia correspondiente
  // que ya definimos en mesh_uvm_pkg.
  // ============================================================

  // 5.1) Broadcast desde una esquina
  class mesh_bcast_corner_test extends mesh_base_test;

  `uvm_component_utils(mesh_bcast_corner_test)

  function new(string name = "mesh_bcast_corner_test",
               uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual task run_phase(uvm_phase phase);
    // Usa el nombre correcto de la secuencia
    mesh_corner_bcast_seq seq;

    phase.raise_objection(this, "Iniciando Broadcast desde esquina");

    seq = mesh_corner_bcast_seq::type_id::create("seq", this);
    seq.start(env.src_agent.seqr);

    #(1000ns);

    phase.drop_objection(this, "Finalizando Broadcast desde esquina");
  endtask

endclass : mesh_bcast_corner_test


  // 5.2) FIFO llena y back-pressure
  class mesh_fifo_backpressure_test extends mesh_base_test;

    `uvm_component_utils(mesh_fifo_backpressure_test)

    function new(string name = "mesh_fifo_backpressure_test",
                 uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
      mesh_fifo_full_backpressure_seq seq;

      phase.raise_objection(this, "Iniciando FIFO llena / back-pressure");

      seq = mesh_fifo_full_backpressure_seq::type_id::create("seq", this);
      seq.start(env.src_agent.seqr);

      // Tal vez mas tiempo para llenar/desllenar FIFOs
      #(5000ns);

      phase.drop_objection(this, "Finalizando FIFO llena / back-pressure");
    endtask

  endclass : mesh_fifo_backpressure_test

  // 5.3) Ruta maxima esquina a esquina
  class mesh_max_route_test extends mesh_base_test;

    `uvm_component_utils(mesh_max_route_test)

    function new(string name = "mesh_max_route_test",
                 uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
      mesh_max_corner_path_seq seq;

      phase.raise_objection(this, "Iniciando Ruta maxima esquina-esquina");

      seq = mesh_max_corner_path_seq::type_id::create("seq", this);
      seq.start(env.src_agent.seqr);

      #(2000ns);

      phase.drop_objection(this, "Finalizando Ruta maxima esquina-esquina");
    endtask

  endclass : mesh_max_route_test

  // 5.4) Contencion fuerte y todos los puertos activos
  class mesh_full_contention_test extends mesh_base_test;

    `uvm_component_utils(mesh_full_contention_test)

    function new(string name = "mesh_full_contention_test",
                 uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
      mesh_full_load_contention_seq seq;

      phase.raise_objection(this, "Iniciando Contencion fuerte / full load");

      seq = mesh_full_load_contention_seq::type_id::create("seq", this);
      seq.start(env.src_agent.seqr);

      #(5000ns);

      phase.drop_objection(this, "Finalizando Contencion fuerte / full load");
    endtask

  endclass : mesh_full_contention_test

  // 5.5) Arbitraje moderado hacia un mismo destino
  class mesh_moderate_arbitration_test extends mesh_base_test;

    `uvm_component_utils(mesh_moderate_arbitration_test)

    function new(string name = "mesh_moderate_arbitration_test",
                 uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
      mesh_moderate_arbitration_seq seq;

      phase.raise_objection(this, "Iniciando Arbitraje moderado a un destino");

      seq = mesh_moderate_arbitration_seq::type_id::create("seq", this);
      seq.start(env.src_agent.seqr);

      #(2000ns);

      phase.drop_objection(this, "Finalizando Arbitraje moderado a un destino");
    endtask

  endclass : mesh_moderate_arbitration_test

  // 5.6) Router como terminal y destino (self-consume)
  class mesh_selfloop_test extends mesh_base_test;

    `uvm_component_utils(mesh_selfloop_test)

    function new(string name = "mesh_selfloop_test",
                 uvm_component parent = null);
      super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
      mesh_self_loopback_seq seq;

      phase.raise_objection(this, "Iniciando Router como terminal y destino");

      seq = mesh_self_loopback_seq::type_id::create("seq", this);
      seq.start(env.src_agent.seqr);

      #(2000ns);

      phase.drop_objection(this, "Finalizando Router como terminal y destino");
    endtask

  endclass : mesh_selfloop_test

endpackage : mesh_test_pkg


// mesh_top_tb.sv
//
// Top-level testbench para la malla 4x4 con UVM.
//
// - Instancia la interface mesh_if.
// - Instancia el DUT mesh_gnrtr.
// - Genera reloj y reset.
// - Conecta el virtual interface al ambiente UVM via config_db.
// - Llama a run_test() (el test se selecciona con +UVM_TESTNAME).

`timescale 1ns/1ps

import uvm_pkg::*;
`include "uvm_macros.svh"

// Importar paquetes de UVM específicos
import mesh_uvm_pkg::*;   // env, agentes, secuencias
import mesh_scoreboard_pkg::*;
import mesh_test_pkg::*;  // tests (mesh_base_test y derivados)


module mesh_top_tb;

  // Parámetros de la malla
  localparam int ROWS   = 4;
  localparam int COLUMS = 4;
  localparam int PCK_W  = 40;

  // Interface de la malla
  mesh_if #(
    .ROWS   (ROWS),
    .COLUMS (COLUMS),
    .PCK_W  (PCK_W)
  ) mesh_if_inst();

  // ------------------------------------------------------------
  // Instancia del DUT
  //
  // Se asume que la definición del módulo mesh_gnrtr coincide
  // con tu testbench "manual":
  //
  //  module mesh_gnrtr #(
  //    parameter int ROWS    = ...,
  //    parameter int COLUMS  = ...,
  //    parameter int pckg_sz = ...
  //  ) (
  //    output logic                  pndng        [NTERMS],
  //    output logic [PCK_W-1:0]      data_out     [NTERMS],
  //    output logic                  popin        [NTERMS],
  //    input  logic                  pop          [NTERMS],
  //    input  logic [PCK_W-1:0]      data_out_i_in[NTERMS],
  //    input  logic                  pndng_i_in   [NTERMS],
  //    input  logic                  clk,
  //    input  logic                  reset
  //  );
  // ------------------------------------------------------------

  mesh_gnrtr #(
    .ROWS    (ROWS),
    .COLUMS  (COLUMS),
    .pckg_sz (PCK_W)
  ) dut (
    .pndng        (mesh_if_inst.pndng),
    .data_out     (mesh_if_inst.data_out),
    .popin        (mesh_if_inst.popin),
    .pop          (mesh_if_inst.pop),
    .data_out_i_in(mesh_if_inst.data_out_i_in),
    .pndng_i_in   (mesh_if_inst.pndng_i_in),
    .clk          (mesh_if_inst.clk),
    .reset        (mesh_if_inst.reset)
  );

  // ------------------------------------------------------------
  // Generación de reloj y reset
  // ------------------------------------------------------------

  // Reloj 100 MHz (periodo 10 ns)
  initial begin
    mesh_if_inst.clk = 0;
    forever #5 mesh_if_inst.clk = ~mesh_if_inst.clk;
  end

  // Reset síncrono simple
  initial begin
    mesh_if_inst.reset = 1'b1;
    // Mantener reset algunos ciclos
    repeat (5) @(posedge mesh_if_inst.clk);
    mesh_if_inst.reset = 1'b0;
  end

  // ------------------------------------------------------------
  // Arranque de UVM
  //
  // - Se pasa el virtual interface a todos los componentes que
  //   llamen a uvm_config_db::get(...,"vif",...).
  // - Se invoca run_test(), dejando que +UVM_TESTNAME seleccione
  //   la clase de test.
  // ------------------------------------------------------------

  initial begin
    // IMPORTANTE:
    // Se asume que en mesh_uvm_pkg existe:
    //   typedef virtual mesh_if.tb mesh_vif_t;
    //
    // Aqui configuramos ese vif para todos los componentes (*).
    uvm_config_db#(mesh_vif_t)::set(null, "*", "vif", mesh_if_inst);

    // Si quieres forzar un test por defecto, puedes hacer:
    // run_test("mesh_rand_connectivity_test");
    //
    // Si prefieres usar +UVM_TESTNAME, solo:
    run_test();
  end

endmodule : mesh_top_tb




 
