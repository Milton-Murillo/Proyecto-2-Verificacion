// Package UVM para la malla 4x4.
// Contiene:
//   - Tipo enumerado para el modo de ruteo.
//   - Transacción mesh_packet como uvm_sequence_item.
//   - Secuencia base para derivar secuencias específicas.
//   - Secuencias de pruebas generales:
//   - Secuencias de casos de esquina:

//`timescale 1ns/1ps
`include "Router_library.sv"     
package mesh_uvm_pkg;

  import uvm_pkg::*;             // Importa todas las definiciones del paquete UVM.
  `include "uvm_macros.svh"      // Incluye macros UVM 
  

  // ------------------------------------------------------------
  // 1) Enumeración de modos de ruta (a nivel de transacción)
  // ------------------------------------------------------------
  //
  // Define los modos de ruteo usados en la transacción UVM.
  // La codificación interna del DUT puede ser distinta.
  // El driver se encarga de mapear este campo enum al bit de modo
  // y a cualquier otro campo necesario en el paquete físico de 40 bits.
  //
  typedef enum bit [1:0] {
    MESH_MODE_ROW_FIRST = 2'b00,  // Modo de ruteo que prioriza desplazamiento por filas.
    MESH_MODE_COL_FIRST = 2'b01,  // Modo de ruteo que prioriza desplazamiento por columnas.
    MESH_MODE_BCAST     = 2'b10   // Modo de ruteo de broadcast hacia múltiples destinos.
  } mesh_mode_e;

  // Representa el paquete lógico de 40 bits a nivel de UVM.
  //
  // Campos del paquete físico según el plan de pruebas:
  //   [39:32] Nxt jump     : valor escrito por el router (Internal Interface ID).
  //   [31:28] Row          : parte del External Interface ID.
  //   [27:24] Column       : parte del External Interface ID.
  //   [23]    Mode         : modo de ruteo (fila, columna o broadcast).
  //   [22:0]  Payload      : datos de mensaje.
  //
  // Campos adicionales para uso del entorno de verificación:
  //   - src_term: terminal origen en la malla (0 a 15).
  //   - dst_term: terminal destino esperado (0 a 15).
  //   - delay_cycles: retardo entre transacciones en ciclos de reloj.
  //   - Campos de metadatos para scoreboard (tiempos y número de saltos).
  //

  // Typedef para el virtual interface usado por drivers y monitores.
  typedef virtual mesh_if mesh_vif_t;

  class mesh_packet extends uvm_sequence_item;

    // Terminal origen en la malla, indexada de 0 a 15.
    rand int unsigned src_term;

    // Coordenadas de destino según el External Interface ID.
    // Se usan para formar los campos de fila y columna del paquete.
    rand bit [3:0] dst_row;
    rand bit [3:0] dst_col;

    // Modo de ruteo a nivel abstracto definido por mesh_mode_e.
    rand mesh_mode_e mode;

    // Campo de datos de 23 bits utilizado como carga útil del paquete.
    rand bit [22:0] payload;

    // Campo Nxt jump de 8 bits, actualizado por el DUT durante el ruteo.
    bit  [7:0] nxt_jump;

    // Terminal destino esperado, derivado de las coordenadas Row y Column.
    int unsigned dst_term;

    // Retardo entre esta transacción y la siguiente en ciclos de reloj.
    rand int unsigned delay_cycles;

    // Metadatos para el scoreboard y análisis temporal.
    time send_time;   // Tiempo de inyección del paquete por el driver.
    time recv_time;   // Tiempo de recepción del paquete en la terminal de destino.
    int  exp_hops;    // Número de saltos esperados que usa el scoreboard como referencia.

    // ----------------------------------------------------------
    // Registro UVM y macros de automatización de campos
    // ----------------------------------------------------------
    //
    // Registra la clase mesh_packet en la factoría UVM y
    // define cómo se empaquetan, imprimen y comparan los campos.
    //
    `uvm_object_utils_begin(mesh_packet)
      `uvm_field_int(src_term,     UVM_ALL_ON)              // Incluye src_term en operaciones UVM estándar.
      `uvm_field_int(dst_row,      UVM_ALL_ON)              // Incluye la fila de destino.
      `uvm_field_int(dst_col,      UVM_ALL_ON)              // Incluye la columna de destino.
      `uvm_field_enum(mesh_mode_e, mode,        UVM_ALL_ON) // Incluye el modo de ruteo como tipo enum.
      `uvm_field_int(payload,      UVM_ALL_ON)              // Incluye el campo de carga útil.
      `uvm_field_int(nxt_jump,     UVM_ALL_ON | UVM_READONLY) // Incluye Nxt jump como campo de solo lectura.
      `uvm_field_int(dst_term,     UVM_ALL_ON)              // Incluye la terminal destino esperada.
      `uvm_field_int(delay_cycles, UVM_ALL_ON)              // Incluye el retardo entre transacciones.
      `uvm_field_int(send_time,    UVM_NOPACK)              // Excluye send_time de empaquetado, solo uso de registro e impresión.
      `uvm_field_int(recv_time,    UVM_NOPACK)              // Excluye recv_time de empaquetado.
      `uvm_field_int(exp_hops,     UVM_ALL_ON)              // Incluye el número de saltos esperados.
    `uvm_object_utils_end

    // ----------------------------------------------------------
    // Constructor
    // ----------------------------------------------------------
    //
    // Crea la instancia de mesh_packet y llama al constructor base.
    //
    function new(string name = "mesh_packet");
      super.new(name);
    endfunction

    // ----------------------------------------------------------
    // Constraints sobre la transacción
    // ----------------------------------------------------------

    // Restringe el rango de las terminales externas a valores válidos de 0 a 15.
    constraint c_src_term_range {
      src_term inside {[0:15]};
    }

    // Restringe el rango básico de filas y columnas.
    // Valores en el rango de 0 a 5 que luego se filtran con c_legal_external_id.
    constraint c_row_col_range {
      dst_row inside {[0:5]};
      dst_col inside {[0:5]};
    }

    // Restringe el retardo entre transacciones a valores entre 3 y 5 ciclos de reloj.
    constraint c_delay {
      delay_cycles inside {[3:5]};
    }

    // Constraint para destinos válidos en la malla
    //
    //   01,02,03,04
    //   10,20,30,40
    //   51,52,53,54
    //   15,25,35,45 
    //
    // Cada par (dst_row, dst_col) representa una terminal externa habilitada.
    constraint c_legal_external_id {
      {dst_row, dst_col} inside {
        {4'd0, 4'd1}, {4'd0, 4'd2}, {4'd0, 4'd3}, {4'd0, 4'd4},  // Terminales 01, 02, 03, 04.
        {4'd1, 4'd0}, {4'd2, 4'd0}, {4'd3, 4'd0}, {4'd4, 4'd0},  // Terminales 10, 20, 30, 40.
        {4'd5, 4'd1}, {4'd5, 4'd2}, {4'd5, 4'd3}, {4'd5, 4'd4},  // Terminales 51, 52, 53, 54.
        {4'd1, 4'd5}, {4'd2, 4'd5}, {4'd3, 4'd5}, {4'd4, 4'd5}   // Terminales 15, 25, 35, 45.
      };
    }

    // Convierte los campos de la transacción en un vector de 40 bits.
    function bit [39:0] to_bits();
      bit [39:0] pkt;
      pkt = '0;                            // Inicializa el paquete en cero.
      pkt[39:32] = nxt_jump;              // Asigna el campo Nxt jump en la parte alta del paquete.
      pkt[31:28] = dst_row;               // Asigna la fila de destino en los bits correspondientes.
      pkt[27:24] = dst_col;               // Asigna la columna de destino.
      pkt[23]    = (mode == MESH_MODE_ROW_FIRST) ? 1'b1 :
                   (mode == MESH_MODE_COL_FIRST) ? 1'b0 :
                   1'b1;                   // Asigna el bit Mode según el valor de mode.
      pkt[22:0]  = payload;               // Asigna la carga útil en los bits menos significativos.
      return pkt;                         // Devuelve el paquete de 40 bits formado.
    endfunction

  endclass : mesh_packet

  // ------------------------------------------------------------
  // 3) Secuencia base: mesh_base_seq
  // ------------------------------------------------------------
  //
  // Declara una secuencia base sobre el tipo de transacción mesh_packet.
  // Sirve como clase padre para secuencias específicas de pruebas.
  //
  class mesh_base_seq extends uvm_sequence #(mesh_packet);

    `uvm_object_utils(mesh_base_seq)      // Registra la secuencia base en la factoría UVM.

    // Constructor de la secuencia base.
    function new(string name = "mesh_base_seq");
      super.new(name);
    endfunction

    // No genera tráfico por sí misma, solo define la estructura a heredar.
    virtual task body();
      // Esta secuencia base no instancia ni envía transacciones.
      // Las secuencias derivadas implementan el patrón de tráfico específico.
    endtask

  endclass : mesh_base_seq
  // ------------------------------------------------------------
  // 4) Secuencia: Conectividad aleatoria
  // Genera tráfico con parámetros aleatorios para verificar rutas
  // entre terminales de la malla bajo modos fila primero y columna primero.
  // ------------------------------------------------------------
  class mesh_rand_connectivity_seq extends mesh_base_seq;

    `uvm_object_utils(mesh_rand_connectivity_seq)

    // Define la cantidad total de paquetes que se envían en la prueba.
    rand int unsigned num_packets;

    // Define el número máximo de terminales origen diferentes activas al mismo tiempo.
    rand int unsigned num_active_src_terms;

    // Restringe el número de paquetes a un rango entre 30 y 50.
    constraint c_num_packets {
      num_packets inside {[30:50]};  // ajustable
    }

    // Restringe el número de terminales origen activas a un rango entre 3 y 10.
    constraint c_num_active_src_terms {
      num_active_src_terms inside {[3:10]};
    }

    function new(string name = "mesh_rand_connectivity_seq");
      super.new(name);
    endfunction

    // Cuerpo de la secuencia que genera y envía transacciones aleatorias.
    virtual task body();
      mesh_packet tr;

      // Emite mensaje inicial con el número de paquetes configurado.
      `uvm_info(get_type_name(),
                $sformatf("Iniciando Conectividad aleatoria: num_packets=%0d",
                          num_packets),
                UVM_MEDIUM)

      // Randomiza los parámetros de la secuencia, incluyendo num_packets y num_active_src_terms.
      if (!randomize()) begin
        `uvm_error(get_type_name(), "Fallo randomize() en mesh_rand_connectivity_seq")
        return;
      end

      // Recorre todas las transacciones que se desean enviar.
      // En cada iteración se crea y se randomiza un nuevo mesh_packet.
      for (int n = 0; n < num_packets; n++) begin

        // Crea una instancia de mesh_packet con nombre identificador según el índice.
        tr = mesh_packet::type_id::create($sformatf("tr_%0d", n), null);

        // Randomiza la transacción restringiendo el modo a fila primero o columna primero.
        if (!tr.randomize() with {
              // En conectividad aleatoria se limita el modo a rutas fila primero o columna primero.
              mode inside {MESH_MODE_ROW_FIRST, MESH_MODE_COL_FIRST};
            }) begin
          `uvm_error(get_type_name(), "Fallo randomize() de mesh_packet en conectividad aleatoria")
          continue;
        end

        // Inicia la transferencia del ítem hacia el driver.
        start_item(tr);
        // Finaliza la transferencia del ítem hacia el driver.
        finish_item(tr);

        // Muestra información resumida del paquete enviado para trazado en el log.
        `uvm_info(get_type_name(),
                  $sformatf("Enviando paquete aleatorio %0d: src_term=%0d row=%0d col=%0d mode=%0d payload=0x%0h delay=%0d",
                            n, tr.src_term, tr.dst_row, tr.dst_col, tr.mode, tr.payload, tr.delay_cycles),
                  UVM_LOW)
      end

      // Emite mensaje final indicando la terminación de la secuencia de conectividad aleatoria.
      `uvm_info(get_type_name(),
                "Finalizando Conectividad aleatoria",
                UVM_MEDIUM)
    endtask

  endclass : mesh_rand_connectivity_seq

  // ------------------------------------------------------------
  // 5) Secuencia: Comparacion de modos de ruta
  // Genera pares de paquetes para un mismo origen y destino,
  // uno con modo fila primero y otro con modo columna primero,
  // con el fin de comparar el comportamiento de ambos modos.
  // ------------------------------------------------------------
  class mesh_compare_modes_seq extends mesh_base_seq;

    `uvm_object_utils(mesh_compare_modes_seq)

    // Define cuántas repeticiones se generan por cada par origen-destino.
    rand int unsigned num_reps_per_pair;

    // Restringe el número de repeticiones entre 3 y 5 por par origen-destino.
    constraint c_num_reps {
      num_reps_per_pair inside {[3:5]};
    }

    function new(string name = "mesh_compare_modes_seq");
      super.new(name);
    endfunction

  // Cuerpo de la secuencia que crea y envía pares de transacciones
  // con modos de ruteo fila primero y columna primero.
  virtual task body();
    mesh_packet tr_row_first;
    mesh_packet tr_col_first;

    // Arreglos dinámicos para almacenar terminales de origen y coordenadas destino.
    int unsigned src_terms[$];
    bit [3:0]    dst_rows[$];
    bit [3:0]    dst_cols[$];
    int unsigned rep;

    // Randomiza parámetros de la secuencia, incluyendo num_reps_per_pair.
    if (!randomize()) begin
      `uvm_error(get_type_name(), "Fallo randomize() en mesh_compare_modes_seq")
      return;
    end

    // Mensaje inicial con el número de repeticiones por par configurado.
    `uvm_info(get_type_name(),
              $sformatf("Iniciando Comparacion de modos de ruta: num_reps_per_pair=%0d",
                        num_reps_per_pair),
              UVM_MEDIUM)

    // Lista de pares origen-destino de tipo esquina a esquina utilizada en la comparación.
    //   - src_term 0 corresponde a una esquina de la malla.
    //   - src_term 3 corresponde a otra esquina.
    //   - src_term 12 y 15 corresponden a esquinas restantes.
    //
    src_terms = '{0, 3, 12, 15};                     // Terminales de origen consideradas.
    dst_rows  = '{4'd5, 4'd0, 4'd5, 4'd0};           // Filas destino asociadas a cada origen.
    dst_cols  = '{4'd4, 4'd1, 4'd1, 4'd4};           // Columnas destino asociadas a cada origen.

    // Recorre cada terminal de origen configurada en src_terms.
    foreach (src_terms[idx]) begin
      // Para cada par origen-destino, repite el envío varias veces.
      for (rep = 0; rep < num_reps_per_pair; rep++) begin

        // Crea un paquete con modo fila primero para el par origen-destino actual.
        tr_row_first = mesh_packet::type_id::create(
          $sformatf("tr_row_first_s%0d_rep%0d", idx, rep), null);

        // Randomiza la transacción fijando origen, fila, columna y modo fila primero.
        if (!tr_row_first.randomize() with {
              src_term == src_terms[idx];
              dst_row  == dst_rows[idx];
              dst_col  == dst_cols[idx];
              mode     == MESH_MODE_ROW_FIRST;
            }) begin
          `uvm_error(get_type_name(), "Fallo randomize() tr_row_first")
          continue;
        end

        // Envía el paquete con modo fila primero.
        start_item(tr_row_first);
        finish_item(tr_row_first);

        // Registra en el log la información del paquete con modo fila primero.
        `uvm_info(get_type_name(),
                  $sformatf("Modo fila primero: src_term=%0d row=%0d col=%0d payload=0x%0h",
                            tr_row_first.src_term, tr_row_first.dst_row,
                            tr_row_first.dst_col, tr_row_first.payload),
                  UVM_LOW)

        // Crea un paquete con modo columna primero para el mismo par origen-destino.
        tr_col_first = mesh_packet::type_id::create(
          $sformatf("tr_col_first_s%0d_rep%0d", idx, rep), null);

        // Randomiza la transacción fijando origen, fila, columna y modo columna primero.
        if (!tr_col_first.randomize() with {
              src_term == src_terms[idx];
              dst_row  == dst_rows[idx];
              dst_col  == dst_cols[idx];
              mode     == MESH_MODE_COL_FIRST;
            }) begin
          `uvm_error(get_type_name(), "Fallo randomize() tr_col_first")
          continue;
        end

        // Envía el paquete con modo columna primero.
        start_item(tr_col_first);
        finish_item(tr_col_first);

        // Registra en el log la información del paquete con modo columna primero.
        `uvm_info(get_type_name(),
                  $sformatf("Modo columna primero: src_term=%0d row=%0d col=%0d payload=0x%0h",
                            tr_col_first.src_term, tr_col_first.dst_row,
                            tr_col_first.dst_col, tr_col_first.payload),
                  UVM_LOW)
      end
    end

    // Mensaje final indicando la finalización de la comparación de modos de ruta.
    `uvm_info(get_type_name(),
              "Finalizando Comparacion de modos de ruta",
              UVM_MEDIUM)
  endtask


  endclass : mesh_compare_modes_seq


// ------------------------------------------------------------
// Secuencia: Broadcast general desde todas las terminales
// Genera tráfico donde cada terminal origen de 0 a 15 envía
// un paquete hacia todos los External IDs válidos con un mismo payload.
// Permite observar el comportamiento de difusión desde múltiples fuentes.
// ------------------------------------------------------------
class mesh_broadcast_all_terms_seq extends mesh_base_seq;

  `uvm_object_utils(mesh_broadcast_all_terms_seq)

  // Define un valor de payload fijo que se usa en todos los paquetes de la secuencia.
  rand bit [22:0] fixed_payload;

  // Restringe el payload para que no tome el valor cero.
  constraint c_fixed_payload_nonzero {
    fixed_payload != 23'd0;
  }

  function new(string name = "mesh_broadcast_all_terms_seq");
    super.new(name);
  endfunction

  // Cuerpo de la secuencia que construye y envía paquetes de broadcast lógico
  // desde todas las terminales hacia todos los destinos externos válidos.
  virtual task body();
    // ================================
    // 1) Declaraciones 
    // ================================
    mesh_packet tr;

    // Lista de fuentes que recorre las terminales 0 a 15.
    int unsigned src_terms[$];

    // Listas de destinos válidos (External ID) como pares fila, columna.
    bit [3:0] dst_rows[$];
    bit [3:0] dst_cols[$];

    int unsigned s_idx;  // Índice para recorrer src_terms.
    int unsigned d_idx;  // Índice para recorrer destinos.

    // ================================
    // 2) Randomizar parámetros de la secuencia
    // ================================
    // Randomiza la secuencia para obtener el valor fixed_payload.
    if (!randomize()) begin
      `uvm_error(get_type_name(), "Fallo randomize() en mesh_broadcast_all_terms_seq")
      return;
    end

    // Mensaje inicial con el payload fijo seleccionado.
    `uvm_info(get_type_name(),
              $sformatf("Iniciando Broadcast general: fixed_payload=0x%0h",
                        fixed_payload),
              UVM_MEDIUM)

    // ================================
    // 3) Construir lista de fuentes 0..15
    // ================================
    // Agrega todas las terminales externas como posibles fuentes de broadcast.
    for (int s = 0; s < 16; s++) begin
      src_terms.push_back(s);
    end

    // ================================
    // 4) Construir lista de todos los External IDs válidos
    //    conjunto de constraint c_legal_external_id del mesh_packet.
    // ================================
    dst_rows = '{
      4'd0,4'd0,4'd0,4'd0,   // Filas para 01, 02, 03, 04.
      4'd1,4'd2,4'd3,4'd4,   // Filas para 10, 20, 30, 40.
      4'd5,4'd5,4'd5,4'd5,   // Filas para 51, 52, 53, 54.
      4'd1,4'd2,4'd3,4'd4    // Filas para 15, 25, 35, 45.
    };

    dst_cols = '{
      4'd1,4'd2,4'd3,4'd4,   // Columnas para 01, 02, 03, 04.
      4'd0,4'd0,4'd0,4'd0,   // Columnas para 10, 20, 30, 40.
      4'd1,4'd2,4'd3,4'd4,   // Columnas para 51, 52, 53, 54.
      4'd5,4'd5,4'd5,4'd5    // Columnas para 15, 25, 35, 45.
    };

    // Muestra el número total de fuentes y destinos utilizados en el broadcast.
    `uvm_info(get_type_name(),
              $sformatf("Broadcast: %0d fuentes, %0d destinos",
                        src_terms.size(), dst_rows.size()),
              UVM_LOW)

    // ================================
    // 5) Broadcast logico:
    //    Para cada fuente se envía un paquete a cada External ID
    //    usando el mismo payload fijo y modos de ruteo permitidos.
    // ================================
    foreach (src_terms[s_idx]) begin
      foreach (dst_rows[d_idx]) begin
        // Crea una transacción de broadcast para la combinación fuente-destino actual.
        tr = mesh_packet::type_id::create(
          $sformatf("bcast_src%0d_dst%0d", src_terms[s_idx], d_idx), null);

        // Randomiza la transacción fijando origen, fila, columna, modo y payload.
        if (!tr.randomize() with {
              src_term == src_terms[s_idx];
              dst_row  == dst_rows[d_idx];
              dst_col  == dst_cols[d_idx];
              mode     inside {MESH_MODE_ROW_FIRST, MESH_MODE_COL_FIRST};
              payload  == fixed_payload;
            }) begin
          `uvm_error(get_type_name(), "Fallo randomize() en broadcast_all_terms")
          continue;
        end

        // Envía el ítem de broadcast al driver.
        start_item(tr);
        finish_item(tr);

        // Registra información detallada del paquete de broadcast enviado.
        `uvm_info(get_type_name(),
                  $sformatf("Broadcast: src=%0d -> row=%0d col=%0d mode=%0d payload=0x%0h delay=%0d",
                            tr.src_term, tr.dst_row, tr.dst_col,
                            tr.mode, tr.payload, tr.delay_cycles),
                  UVM_LOW)
      end
    end

    // Mensaje final indicando la finalización del broadcast general.
    `uvm_info(get_type_name(),
              "Finalizando Broadcast general desde todas las terminales",
              UVM_MEDIUM)
  endtask

endclass : mesh_broadcast_all_terms_seq

//=================================
  // Secuencia de caso de esquina: FIFO llena y back-pressure
  // Genera trafico intenso desde varias fuentes hacia pocos destinos
  // para ocupar las FIFOs internas y provocar back-pressure en la malla.
  // ==================================================================
  class mesh_fifo_full_backpressure_seq extends mesh_base_seq;

    `uvm_object_utils(mesh_fifo_full_backpressure_seq)

    // Define la cantidad de terminales fuente activas que inyectan trafico.
    rand int unsigned num_src_terms;

    // Define la cantidad de paquetes transmitidos por cada fuente activa.
    rand int unsigned num_packets_per_src;

    // Define la cantidad de destinos hotspot que concentran el trafico.
    rand int unsigned num_hotspot_dests;

    // Limita el numero de fuentes activas a un rango de 3 a 8.
    constraint c_num_src_terms {
      num_src_terms inside {[3:8]};         // de 3 a 8 fuentes
    }

    // Limita el numero de paquetes por fuente a un rango de 10 a 15
    constraint c_num_packets_per_src {
      num_packets_per_src inside {[10:15]};  // varios paquetes por fuente
    }

    // Limita la cantidad de destinos hotspot a un rango de 1 a 3.
    constraint c_num_hotspot_dests {
      num_hotspot_dests inside {[1:3]};     // 1 a 3 destinos
    }

    function new(string name = "mesh_fifo_full_backpressure_seq");
      super.new(name);
    endfunction

  // Cuerpo de la secuencia que genera trafico hacia destinos 
  virtual task body();
    mesh_packet tr;

    // Declaraciones de estructuras auxiliares 
    int unsigned src_terms[$];      // lista de fuentes activas
    int unsigned candidate;         // candidato a fuente

    bit [3:0] hotspot_rows[$];      // filas de destinos hotspot
    bit [3:0] hotspot_cols[$];      // columnas de destinos hotspot

    bit [3:0] r, c;                 // variables temporales para elegir hotspot
    bit       found;                // bandera para evitar hotspots duplicados

    int unsigned h_idx;             // indice de hotspot
    int         p;                  // indice del paquete en el for
    int         s_idx;              // indice de la fuente en foreach

    // Randomiza los parametros de la secuencia: fuentes, paquetes y hotspots.
    if (!randomize()) begin
      `uvm_error(get_type_name(), "Fallo randomize() en mesh_fifo_full_backpressure_seq")
      return;
    end

    // Construye la lista de fuentes activas sin repetir ninguna terminal.
    while (src_terms.size() < num_src_terms) begin
      void'(std::randomize(candidate) with { candidate inside {[0:15]}; });
      if (!(candidate inside {src_terms})) begin
        src_terms.push_back(candidate);
      end
    end

    // Construye la lista de destinos hotspot como pares (row,col) validos.
    while (hotspot_rows.size() < num_hotspot_dests) begin
      // Elige un par (r,c) legal en la malla exterior.
      void'(std::randomize(r, c) with {
        {r, c} inside {
          {4'd0, 4'd1}, {4'd0, 4'd2}, {4'd0, 4'd3}, {4'd0, 4'd4},
          {4'd1, 4'd0}, {4'd2, 4'd0}, {4'd3, 4'd0}, {4'd4, 4'd0},
          {4'd5, 4'd1}, {4'd5, 4'd2}, {4'd5, 4'd3}, {4'd5, 4'd4},
          {4'd1, 4'd5}, {4'd2, 4'd5}, {4'd3, 4'd5}, {4'd4, 4'd5}
        };
      });

      // Verifica que el destino elegido no se encuentre repetido en la lista actual.
      found = 1'b0;
      foreach (hotspot_rows[i]) begin
        if (hotspot_rows[i] == r && hotspot_cols[i] == c)
          found = 1'b1;
      end

      // Agrega el nuevo hotspot si aun no existe en la lista.
      if (!found) begin
        hotspot_rows.push_back(r);
        hotspot_cols.push_back(c);
      end
    end

    // Muestra configuracion general de la prueba para trazado en log.
    `uvm_info(get_type_name(),
              $sformatf("FIFO llena/back-pressure: num_src_terms=%0d num_packets_per_src=%0d num_hotspots=%0d",
                        num_src_terms, num_packets_per_src, num_hotspot_dests),
              UVM_MEDIUM)

    // Genera trafico intenso: cada fuente envia varios paquetes
    // concentrados en los destinos definidos.
    foreach (src_terms[s_idx]) begin
      for (p = 0; p < num_packets_per_src; p++) begin

        // Crea una transaccion asociada a la fuente y al indice de paquete.
        tr = mesh_packet::type_id::create(
          $sformatf("fifo_full_src%0d_pkt%0d", src_terms[s_idx], p), null);

        // Elige uno de los destinos por indice.
        void'(std::randomize(h_idx) with {
          h_idx inside {[0:hotspot_rows.size()-1]};
        });

        // Randomiza la transaccion fijando fuente, destino y modo de ruteo permitido.
        if (!tr.randomize() with {
              src_term == src_terms[s_idx];
              dst_row  == hotspot_rows[h_idx];
              dst_col  == hotspot_cols[h_idx];
              mode     inside {MESH_MODE_ROW_FIRST, MESH_MODE_COL_FIRST};
            }) begin
          `uvm_error(get_type_name(), "Fallo randomize() en fifo_full_backpressure")
          continue;
        end

        // Entrega la transaccion al driver para su envio.
        start_item(tr);
        finish_item(tr);

        // Registra detalles del paquete enviado en esta secuencia de FIFO llena.
        `uvm_info(get_type_name(),
                  $sformatf("FIFO-full: src=%0d -> row=%0d col=%0d payload=0x%0h delay=%0d",
                            tr.src_term, tr.dst_row, tr.dst_col,
                            tr.payload, tr.delay_cycles),
                  UVM_LOW)
      end
    end

    // Indica el final de la secuencia de FIFO llena y back-pressure.
    `uvm_info(get_type_name(),
              "Finalizando FIFO llena y back-pressure",
              UVM_MEDIUM)
  endtask


  endclass : mesh_fifo_full_backpressure_seq


  // ==================================================================
  // Secuencia de caso de esquina:
  //     Contencion fuerte y todos los puertos activos
  // Genera trafico de carga maxima desde casi todas las terminales
  // hacia un conjunto reducido de destinos
  // ==================================================================
  class mesh_full_load_contention_seq extends mesh_base_seq;

    `uvm_object_utils(mesh_full_load_contention_seq)

    // Define la cantidad de paquetes enviados por cada terminal fuente.
    rand int unsigned num_packets_per_src;

    // Define la cantidad de destinos utilizados en esta secuencia.
    rand int unsigned num_hotspot_dests;

    // Limita el numero de paquetes por fuente a un rango de 10 a 30.
    constraint c_num_packets {
      num_packets_per_src inside {[10:30]};
    }

    // Limita el numero de destinos a un rango de 3 a 5.
    constraint c_num_hotspot_dests {
      num_hotspot_dests inside {[3:5]}; 
    }

    function new(string name = "mesh_full_load_contention_seq");
      super.new(name);
    endfunction

    // secuencia que activa todas las fuentes
    // y concentra el trafico en los destinos hotspot.
    virtual task body();
      // ================================
      // 1) Declaraciones
      // ================================
      mesh_packet tr;

      // Lista de fuentes, incluyendo las terminales 0 a 15.
      int unsigned src_terms[$];

      // Listas de destinos representados como pares (row,col).
      bit [3:0] hotspot_rows[$];
      bit [3:0] hotspot_cols[$];

      // Indices y auxiliares para iteraciones 
      int s;                    // indice de fuente
      int p;                    // indice de paquete
      int i;                    // indice para buscar duplicados
      int h;                    // indice para imprimir hotspots
      int unsigned h_idx;       // indice de destino elegido

      // Variables temporales para generar destinos 
      bit [3:0] r_row, r_col;
      bit       found;

      // ================================
      // 2) Randomizacion de la secuencia
      // ================================
      // Randomiza parametros como num_packets_per_src y num_hotspot_dests.
      if (!randomize()) begin
        `uvm_error(get_type_name(),
                   "Fallo randomize() en mesh_full_load_contention_seq")
        return;
      end

      // Mensaje inicial con el resumen de configuracion de la prueba.
      `uvm_info(get_type_name(),
                $sformatf("Iniciando Contencion fuerte/todos activos: num_packets_per_src=%0d num_hotspots=%0d",
                          num_packets_per_src, num_hotspot_dests),
                UVM_MEDIUM)

      // ================================
      // 3) Construir lista de fuentes 0..15
      // ================================
      // Llena src_terms con todas las terminales posibles como fuentes.
      for (s = 0; s < 16; s++) begin
        src_terms.push_back(s);
      end

      // ================================
      // 4) Construir lista de destinos 
      //    Cada destino es un (row,col) valido segun c_legal_external_id.
      // ================================
      while (hotspot_rows.size() < num_hotspot_dests) begin
        // Elige un destino valido al azar dentro del conjunto de External IDs.
        void'(std::randomize(r_row, r_col) with {
          {r_row, r_col} inside {
            {4'd0, 4'd1}, {4'd0, 4'd2}, {4'd0, 4'd3}, {4'd0, 4'd4},
            {4'd1, 4'd0}, {4'd2, 4'd0}, {4'd3, 4'd0}, {4'd4, 4'd0},
            {4'd5, 4'd1}, {4'd5, 4'd2}, {4'd5, 4'd3}, {4'd5, 4'd4},
            {4'd1, 4'd5}, {4'd2, 4'd5}, {4'd3, 4'd5}, {4'd4, 4'd5}
          };
        });

        // Evita agregar destinos repetidos.
        found = 0;
        foreach (hotspot_rows[i]) begin
          if (hotspot_rows[i] == r_row && hotspot_cols[i] == r_col)
            found = 1;
        end

        // Agrega el nuevo destino si no existe previamente.
        if (!found) begin
          hotspot_rows.push_back(r_row);
          hotspot_cols.push_back(r_col);
        end
      end

      // Informa cuantos destinos fueron definidos.
      `uvm_info(get_type_name(),
                $sformatf("Hotspots definidos: %0d destinos", hotspot_rows.size()),
                UVM_LOW)

      // Muestra cada destino con sus coordenadas fila y columna.
      foreach (hotspot_rows[h]) begin
        `uvm_info(get_type_name(),
                  $sformatf("  Hotspot %0d -> row=%0d col=%0d",
                            h, hotspot_rows[h], hotspot_cols[h]),
                  UVM_LOW)
      end

      // ================================
      // 5) Trafico de carga maxima:
      //    Todas las fuentes activas envian paquetes a los destinos.
      // ================================
      foreach (src_terms[s_idx]) begin
        for (p = 0; p < num_packets_per_src; p++) begin
          // Crea una transaccion asociada a la fuente y al indice de paquete.
          tr = mesh_packet::type_id::create(
            $sformatf("full_load_src%0d_pkt%0d", src_terms[s_idx], p), null);

          // Elige un destino hotspot para la transaccion.
          void'(std::randomize(h_idx) with {
            h_idx inside {[0:hotspot_rows.size()-1]};
          });

          // Randomiza la transaccion forzando que el destino sea el destino seleccionado.
          if (!tr.randomize() with {
                src_term == src_terms[s_idx];
                dst_row  == hotspot_rows[h_idx];
                dst_col  == hotspot_cols[h_idx];
                mode     inside {MESH_MODE_ROW_FIRST, MESH_MODE_COL_FIRST};
              }) begin
            `uvm_error(get_type_name(),
                       $sformatf("Fallo randomize() en full_load para src=%0d hotspot_idx=%0d row=%0d col=%0d",
                                 src_terms[s_idx], h_idx,
                                 hotspot_rows[h_idx], hotspot_cols[h_idx]))
            continue;
          end

          // Entrega el item al driver para su envio hacia el DUT.
          start_item(tr);
          finish_item(tr);

          // Registra cada paquete de carga maxima enviado hacia los destinos.
          `uvm_info(get_type_name(),
                    $sformatf("Full-load: src=%0d -> row=%0d col=%0d mode=%0d payload=0x%0h delay=%0d",
                              tr.src_term, tr.dst_row, tr.dst_col,
                              tr.mode, tr.payload, tr.delay_cycles),
                    UVM_LOW)
        end
      end

      // Mensaje final de cierre de la secuencia de contencion fuerte.
      `uvm_info(get_type_name(),
                "Finalizando Contencion fuerte/todos los puertos activos",
                UVM_MEDIUM)
    endtask

  endclass : mesh_full_load_contention_seq



  // ==================================================================
  // Secuencia de caso de esquina:
  //     Arbitraje moderado hacia un mismo destino
  // Genera trafico desde varias fuentes hacia un unico destino comun
  // para observar el comportamiento de arbitraje en la malla.
  // ==================================================================
  class mesh_moderate_arbitration_seq extends mesh_base_seq;

    `uvm_object_utils(mesh_moderate_arbitration_seq)

    // Define la cantidad de fuentes que compiten por el mismo destino.
    rand int unsigned num_src_terms;

    // Define la cantidad de paquetes generados por cada fuente.
    rand int unsigned num_packets_per_src;

    // Define la fila del destino comun para todas las fuentes.
    rand bit [3:0] target_row;
    // Define la columna del destino comun para todas las fuentes.
    rand bit [3:0] target_col;

    // Limita el numero de fuentes contendientes a un rango de 2 a 4.
    constraint c_num_src_terms_mod {
      num_src_terms inside {[2:4]};
    }

    // Limita el numero de paquetes por fuente a un rango de 3 a 10.
    constraint c_num_packets_mod {
      num_packets_per_src inside {[3:10]};
    }

    // Restringe el destino comun a un External ID valido en la malla.
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

  // Cuerpo de la secuencia que genera trafico hacia un mismo destino.
  virtual task body();
    // =================================
    // 1) Declaraciones 
    // =================================
    mesh_packet tr;

    // Lista de fuentes seleccionadas sin repetir.
    int unsigned src_terms[$];
    int unsigned candidate;

    // Indices para recorrer fuentes y paquetes.
    int s_idx;  // indice para foreach de src_terms
    int p;      // indice para paquetes por fuente

    // =================================
    // 2) Randomizacion de la secuencia
    // =================================
    // Randomiza parametros como numero de fuentes, paquetes y destino comun.
    if (!randomize()) begin
      `uvm_error(get_type_name(), "Fallo randomize() en mesh_moderate_arbitration_seq")
      return;
    end

    // =================================
    // 3) Seleccion de fuentes sin repetir
    // =================================
    //
    // Construye src_terms con num_src_terms terminales distintas
    // tomadas aleatoriamente del rango 0 a 15.
    //
    while (src_terms.size() < num_src_terms) begin
      void'(std::randomize(candidate) with { candidate inside {[0:15]}; });

      if (!(candidate inside {src_terms})) begin
        src_terms.push_back(candidate);
      end
    end

    // Informa la configuracion final de la secuencia de arbitraje moderado.
    `uvm_info(get_type_name(),
              $sformatf("Arbitraje moderado: num_src_terms=%0d num_packets_per_src=%0d destino=(%0d,%0d)",
                        num_src_terms, num_packets_per_src,
                        target_row, target_col),
              UVM_MEDIUM)

    // =================================
    // 4) Generacion de trafico hacia un mismo destino
    // =================================
    //
    // Para cada fuente seleccionada se generan varios paquetes
    // que comparten el mismo destino (target_row, target_col).
    //
    foreach (src_terms[s_idx]) begin
      for (p = 0; p < num_packets_per_src; p++) begin
        // Crea una transaccion para la fuente y el indice de paquete actual.
        tr = mesh_packet::type_id::create(
          $sformatf("mod_arb_src%0d_pkt%0d", src_terms[s_idx], p), null);

        // Randomiza la transaccion fijando la fuente y el destino comun.
        if (!tr.randomize() with {
              src_term == src_terms[s_idx];
              dst_row  == target_row;
              dst_col  == target_col;
              mode     inside {MESH_MODE_ROW_FIRST, MESH_MODE_COL_FIRST};
            }) begin
          `uvm_error(get_type_name(), "Fallo randomize() en moderate_arbitration")
          continue;
        end

        // Envía el item al driver para que lo traslade al DUT.
        start_item(tr);
        finish_item(tr);

        // Registra la informacion del paquete enviado hacia el destino comun.
        `uvm_info(get_type_name(),
                  $sformatf("Moderate arb: src=%0d -> row=%0d col=%0d payload=0x%0h delay=%0d",
                            tr.src_term, tr.dst_row, tr.dst_col,
                            tr.payload, tr.delay_cycles),
                  UVM_LOW)
      end
    end

    // Mensaje final que indica el cierre de la secuencia de arbitraje moderado.
    `uvm_info(get_type_name(),
              "Finalizando Arbitraje moderado hacia un mismo destino",
              UVM_MEDIUM)
  endtask


  endclass : mesh_moderate_arbitration_seq

  // ==================================================================
  //  Secuencia de caso de esquina:
  //     Router como terminal y destino (loopback)
  // Genera trafico donde la terminal origen y el destino asociado
  // corresponden al mismo External ID, simulando un caso de loopback.
  // ==================================================================
  class mesh_self_loopback_seq extends mesh_base_seq;

    `uvm_object_utils(mesh_self_loopback_seq)

    // Define la cantidad de terminales que se probaran con trafico loopback.
    rand int unsigned num_loop_terms;

    // Define la cantidad de paquetes generados por cada terminal en loopback.
    rand int unsigned num_packets_per_term;

    // Limita el numero de terminales en loopback a un rango de 3 a 8.
    constraint c_num_loop_terms {
      num_loop_terms inside {[3:8]};
    }

    // Limita el numero de paquetes por terminal a un rango de 1 a 5.
    constraint c_num_packets_loop {
      num_packets_per_term inside {[1:5]};
    }

    function new(string name = "mesh_self_loopback_seq");
      super.new(name);
    endfunction

    // Funcion auxiliar que mapea un src_term a un par (row,col) coherente.
    // Mantiene la correspondencia entre terminal externa y External ID.
    function void map_term_to_row_col(input int unsigned term,
                                      output bit [3:0] r,
                                      output bit [3:0] c);
      // Asignacion directa de pares (row,col) para cada terminal externa.
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

  // Cuerpo de la secuencia que genera paquetes de loopback.
  virtual task body();
    // =================================
    // 1) Declaraciones 
    // =================================
    mesh_packet tr;

    // Lista de terminales que se usaran en modo loopback.
    int unsigned loop_terms[$];
    int unsigned candidate;

    // Indices y variables auxiliares de control.
    int idx;           // indice para foreach(loop_terms[idx])
    int p;             // indice para paquetes por terminal
    bit [3:0] r, c;    // fila y columna asociadas a cada terminal

    // =================================
    // 2) Randomizacion de la secuencia
    // =================================
    // Randomiza parametros como numero de terminales y paquetes por terminal.
    if (!randomize()) begin
      `uvm_error(get_type_name(), "Fallo randomize() en mesh_self_loopback_seq")
      return;
    end

    // =================================
    // 3) Seleccion de terminales en loopback
    // =================================
    //
    // Construye loop_terms con num_loop_terms terminales distintas
    // seleccionadas aleatoriamente del rango 0 a 15.
    //
    while (loop_terms.size() < num_loop_terms) begin
      void'(std::randomize(candidate) with { candidate inside {[0:15]}; });
      if (!(candidate inside {loop_terms})) begin
        loop_terms.push_back(candidate);
      end
    end

    // Mensaje inicial que resume terminales y paquetes por terminal.
    `uvm_info(get_type_name(),
              $sformatf("Router como terminal y destino: num_loop_terms=%0d num_packets_per_term=%0d",
                        num_loop_terms, num_packets_per_term),
              UVM_MEDIUM)

    // =================================
    // 4) Generacion de trafico loopback
    // =================================
    //
    // Para cada terminal seleccionada:
    //   se obtienen sus coordenadas (row,col) y se crean paquetes
    //   donde origen y destino corresponden al mismo External ID.
    //
    foreach (loop_terms[idx]) begin
      // Obtiene las coordenadas asociadas a la terminal en cuestion.
      map_term_to_row_col(loop_terms[idx], r, c);

      for (p = 0; p < num_packets_per_term; p++) begin
        // Crea una transaccion identificada por terminal e indice de paquete.
        tr = mesh_packet::type_id::create(
          $sformatf("loopback_term%0d_pkt%0d", loop_terms[idx], p), null);

        // Randomiza la transaccion para que src_term y destino coincidan en External ID.
        if (!tr.randomize() with {
              src_term == loop_terms[idx];
              dst_row  == r;
              dst_col  == c;
              mode     inside {MESH_MODE_ROW_FIRST, MESH_MODE_COL_FIRST};
            }) begin
          `uvm_error(get_type_name(), "Fallo randomize() en self_loopback")
          continue;
        end

        // Envia el item al driver para ejecutar el trafico de loopback.
        start_item(tr);
        finish_item(tr);

        // Registra la informacion de cada paquete de loopback enviado.
        `uvm_info(get_type_name(),
                  $sformatf("Loopback: term=%0d -> row=%0d col=%0d payload=0x%0h delay=%0d",
                            tr.src_term, tr.dst_row, tr.dst_col,
                            tr.payload, tr.delay_cycles),
                  UVM_LOW)
      end
    end

    // Mensaje final indicando el cierre de la prueba de loopback.
    `uvm_info(get_type_name(),
              "Finalizando Router como terminal y destino",
              UVM_MEDIUM)
  endtask


  endclass : mesh_self_loopback_seq


// ------------------------------------------------------------
// Secuencia "corner case" de destinos invalidos
// Genera paquetes con pares (row,col) fuera del conjunto de
// External IDs validos, para ejercitar el manejo de destinos no mapeados.
// ------------------------------------------------------------
class mesh_invalid_external_id_seq extends mesh_base_seq;

  `uvm_object_utils(mesh_invalid_external_id_seq)

  // Define el numero de paquetes invalidos generados por cada fuente.
  rand int unsigned num_invalid_per_src;

  // Define el numero de terminales fuente activas usadas en la secuencia.
  rand int unsigned num_src_terms;

  // Limita el numero de paquetes invalidos por fuente a un rango de 25 a 40.
  constraint c_num_invalid_per_src {
    num_invalid_per_src inside {[25:40]};
  }

  // Limita el numero de fuentes distintas a un rango de 3 a 15.
  constraint c_num_src_terms {
    num_src_terms inside {[3:15]};
  }

  function new(string name = "mesh_invalid_external_id_seq");
    super.new(name);
  endfunction

  // Cuerpo de la secuencia que genera destinos invalidos.
  virtual task body();
    mesh_packet tr;

    // Lista de fuentes que forma un subconjunto aleatorio de 0 a 15.
    int unsigned src_terms[$];
    int unsigned s_idx;
    int         p;

    int unsigned candidate; // valor temporal para seleccionar fuentes sin repetir

    // Randomiza los parametros de la secuencia: fuentes y paquetes invalidos por fuente.
    if (!randomize()) begin
      `uvm_error(get_type_name(),
                 "Fallo randomize() en mesh_invalid_external_id_seq")
      return;
    end

    // Muestra configuracion inicial de la secuencia de destinos invalidos.
    `uvm_info(get_type_name(),
              $sformatf("Iniciando secuencia de destinos INVALIDOS: num_invalid_per_src=%0d num_src_terms=%0d",
                        num_invalid_per_src, num_src_terms),
              UVM_MEDIUM)

    // Construye un subconjunto aleatorio de fuentes 0..15 sin repetir.
    while (src_terms.size() < num_src_terms) begin
      void'(std::randomize(candidate) with { candidate inside {[0:15]}; });
      if (!(candidate inside {src_terms})) begin
        src_terms.push_back(candidate);
      end
    end

    // Para cada fuente seleccionada, genera varios paquetes con destinos no mapeados.
    foreach (src_terms[s_idx]) begin
      for (p = 0; p < num_invalid_per_src; p++) begin

        // Crea una transaccion identificada por la fuente y el indice de paquete.
        tr = mesh_packet::type_id::create(
               $sformatf("invalid_dst_src%0d_pkt%0d", src_terms[s_idx], p),
               null);

        // Desactiva el constraint de destinos legales para permitir valores fuera del conjunto valido.
        tr.c_legal_external_id.constraint_mode(0);

        // Randomiza la transaccion forzando que el par (dst_row,dst_col)
        // quede fuera del conjunto de External IDs legales.
        if (!tr.randomize() with {
              src_term == src_terms[s_idx];
              mode     inside {MESH_MODE_ROW_FIRST, MESH_MODE_COL_FIRST};

              // Mantiene el rango 0..5 pero exige salir del conjunto legal.
              dst_row inside {[0:5]};
              dst_col inside {[0:5]};

              !(
                (dst_row == 4'd0 && dst_col inside {4'd1,4'd2,4'd3,4'd4}) ||
                (dst_col == 4'd0 && dst_row inside {4'd1,4'd2,4'd3,4'd4}) ||
                (dst_row == 4'd5 && dst_col inside {4'd1,4'd2,4'd3,4'd4}) ||
                (dst_col == 4'd5 && dst_row inside {4'd1,4'd2,4'd3,4'd4})
              );
            }) begin
          `uvm_error(get_type_name(),
                     "Fallo randomize() en mesh_invalid_external_id_seq")
          continue;
        end

        // Entrega el item con destino invalido al driver.
        start_item(tr);
        finish_item(tr);

        // Registra la informacion del paquete con destino invalido generado.
        `uvm_info(get_type_name(),
                  $sformatf("INVALID: src=%0d -> row=%0d col=%0d mode=%0d payload=0x%0h delay=%0d",
                            tr.src_term, tr.dst_row, tr.dst_col,
                            tr.mode, tr.payload, tr.delay_cycles),
                  UVM_LOW)
      end
    end

    // Mensaje final indicando que termina la secuencia de destinos invalidos.
    `uvm_info(get_type_name(),
              "Finalizando secuencia de destinos INVALIDOS",
              UVM_MEDIUM)
  endtask

endclass : mesh_invalid_external_id_seq

/////////////////////////////////////////////////////////////////////////////////////////////////////
  // ------------------------------------------------------------
  // Evento de salida hacia el scoreboard: mesh_out_event
  // Clase usada para reportar un paquete observado en una terminal.
  // Contiene los campos decodificados, el vector completo y el tiempo de recepción.
  // ------------------------------------------------------------
  class mesh_out_event extends uvm_object;

    `uvm_object_utils(mesh_out_event)   // Registro en la factoría UVM.

    // Terminal donde el DUT realizó el pop del paquete.
    int unsigned dst_term;

    // Campos decodificados del paquete de 40 bits.
    bit [7:0]   nxt_jump;
    bit [3:0]   dst_row;
    bit [3:0]   dst_col;
    mesh_mode_e mode;
    bit [22:0]  payload;

    // Paquete completo entregado por el DUT.
    bit [39:0]  data;

    // Tiempo en que la terminal recibió el paquete.
    time recv_time;

    // Constructor del objeto.
    function new(string name = "mesh_out_event");
      super.new(name);
    endfunction

  endclass : mesh_out_event



// ===============================================================
// Sequencer de entrada: mesh_sequencer
// Recibe las secuencias y suministra mesh_packet al driver.
// ===============================================================
class mesh_sequencer extends uvm_sequencer #(mesh_packet);

  `uvm_component_utils(mesh_sequencer)   // Registro en la fabrica UVM.

  // Constructor del sequencer.
  function new(string name = "mesh_sequencer", uvm_component parent = null);
    super.new(name, parent);
  endfunction

endclass : mesh_sequencer

// ===============================================================
// Driver de entrada: mesh_driver
//
// Encargado de recibir mesh_packet desde el sequencer,
// convertirlo en un vector de 40 bits y manejar el handshake
// con el DUT mediante pndng_i_in y popin. Registra send_time
// cuando el DUT acepta el paquete.
// ===============================================================

class mesh_driver extends uvm_driver #(mesh_packet);

  `uvm_component_utils(mesh_driver)

  // Virtual interface que conecta el driver con las señales del DUT
  mesh_vif_t vif;

  // Número total de terminales usadas en la malla
  localparam int NTERMS = 16;

  function new(string name = "mesh_driver", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  // Obtiene el virtual interface desde la config DB
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(mesh_vif_t)::get(this, "", "vif", vif)) begin
      `uvm_fatal(get_type_name(),
                 "No se pudo obtener el virtual interface 'vif' para mesh_driver")
    end
  endfunction

  // Bucle principal del driver que inyecta paquetes al DUT
  virtual task run_phase(uvm_phase phase);
    mesh_packet tr;
    bit [39:0] pkt_bits;
    int unsigned s;

    // Inicializa señales hacia el DUT
    for (s = 0; s < NTERMS; s++) begin
      vif.pndng_i_in[s]    <= 1'b0;
      vif.data_out_i_in[s] <= '0;
    end

    forever begin
      // Recibe transacción desde el sequencer
      seq_item_port.get_next_item(tr);

      s = tr.src_term;
      if (s >= NTERMS) begin
        `uvm_error(get_type_name(),
                   $sformatf("src_term=%0d fuera de rango (NTERMS=%0d)", s, NTERMS))
        seq_item_port.item_done();
        continue;
      end

      // Convierte la transacción al vector de 40 bits
      pkt_bits = tr.to_bits();

      // Aplica retardo especificado por la transacción
      repeat (tr.delay_cycles) @(posedge vif.clk);

      `uvm_info(get_type_name(),
                $sformatf("Driver: enviando paquete desde src_term=%0d bits=%h delay=%0d",
                          s, pkt_bits, tr.delay_cycles),
                UVM_LOW)

      // Coloca el paquete en la terminal indicada y marca pendiente
      @(posedge vif.clk);
      vif.data_out_i_in[s] <= pkt_bits;
      vif.pndng_i_in[s]    <= 1'b1;

      // Espera a que el DUT consuma el paquete usando popin
      @(posedge vif.clk);
      wait (vif.popin[s] == 1'b1);

      // Registra el tiempo de aceptación del DUT
      tr.send_time = $time;

      `uvm_info(get_type_name(),
                $sformatf("Driver: DUT hizo popin en src_term=%0d tiempo=%0t",
                          s, tr.send_time),
                UVM_LOW)

      // Limpia señales en el siguiente ciclo
      @(posedge vif.clk);
      vif.pndng_i_in[s]    <= 1'b0;
      vif.data_out_i_in[s] <= '0;

      // Indica al sequencer que el item terminó
      seq_item_port.item_done();
    end
  endtask

endclass : mesh_driver



// ===============================================================
// Monitor de entrada: mesh_src_monitor
//
// Observa pndng_i_in, data_out_i_in y popin. Detecta flanco
// ascendente de popin para identificar aceptación del DUT.
// Decodifica el paquete de entrada y lo envía al scoreboard
// mediante un analysis_port. También registra cobertura.
// ===============================================================

class mesh_src_monitor extends uvm_component;

  `uvm_component_utils(mesh_src_monitor)

  // Interface hacia el DUT
  mesh_vif_t vif;

  // Puerto para enviar eventos al scoreboard
  uvm_analysis_port #(mesh_packet) ap;

  // Número de terminales
  localparam int NTERMS = 16;

  // Registro de popin anterior para detección de flancos
  bit prev_popin[NTERMS];

  // Variable usada para cobertura
  mesh_packet cov_tr;

  // Covergroup que registra uso de terminales, coordenadas y modos
  covergroup cg_src_h;
    coverpoint cov_tr.src_term {
      bins all_terms[] = {[0:15]};
    }

    coverpoint cov_tr.dst_row {
      bins dir_vals[] = {[0:5]};
    }
    
    coverpoint cov_tr.dst_col {
      bins dir_vals[] = {[0:5]};
    }
    
    coverpoint cov_tr.payload;

    coverpoint cov_tr.mode {
      bins row_first = {MESH_MODE_ROW_FIRST};
      bins col_first = {MESH_MODE_COL_FIRST};
    }
  endgroup

  function new(string name = "mesh_src_monitor", uvm_component parent = null);
    super.new(name, parent);
    ap = new("ap", this);
    cg_src_h = new();
  endfunction

  // Obtiene el virtual interface desde la config DB
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(mesh_vif_t)::get(this, "", "vif", vif)) begin
      `uvm_fatal(get_type_name(),
                 "No se pudo obtener el virtual interface 'vif' para mesh_src_monitor")
    end
  endfunction

  // Bucle de captura de paquetes aceptados por el DUT
  virtual task run_phase(uvm_phase phase);
    bit [39:0] pkt_bits;
    mesh_packet tr;

    // Inicializa historial de popin
    for (int t = 0; t < NTERMS; t++) begin
      prev_popin[t] = 1'b0;
    end

    forever begin
      @(posedge vif.clk);
      if (vif.reset) begin
        // Mientras reset está activo se limpia historial
        for (int t = 0; t < NTERMS; t++) begin
          prev_popin[t] = 1'b0;
        end
      end
      else begin
        // Revisa cada terminal para detectar flanco ascendente de popin
        for (int t = 0; t < NTERMS; t++) begin

          // Detecta aceptación de paquete en terminal t
          if ((vif.popin[t] == 1'b1) && (prev_popin[t] == 1'b0)) begin

            // Obtiene el vector de 40 bits
            pkt_bits = vif.data_out_i_in[t];

            // Crea transacción asociada al evento
            tr = mesh_packet::type_id::create(
                   $sformatf("src_mon_tr_term%0d_time%0t", t, $time), this);

            tr.src_term  = t;
            tr.send_time = $time;

            // Decodifica los campos del paquete
            tr.nxt_jump = pkt_bits[39:32];
            tr.dst_row  = pkt_bits[31:28];
            tr.dst_col  = pkt_bits[27:24];
            tr.mode     = (pkt_bits[23] == 1'b1) ?
                           MESH_MODE_ROW_FIRST : MESH_MODE_COL_FIRST;
            tr.payload  = pkt_bits[22:0];

            `uvm_info(get_type_name(),
                      $sformatf("Monitor SRC: popin en term=%0d tiempo=%0t bits=%h row=%0d col=%0d mode=%0d payload=0x%0h",
                                t, tr.send_time, pkt_bits,
                                tr.dst_row, tr.dst_col, tr.mode, tr.payload),
                      UVM_LOW)

            // Muestra cobertura para esta transacción
            cov_tr = tr;
            cg_src_h.sample();

            // Envia transacción al scoreboard
            ap.write(tr);
          end

          // Actualiza valor previo de popin
          prev_popin[t] = vif.popin[t];
        end
      end
    end
  endtask

endclass : mesh_src_monitor



// ===============================================================
// Agente de entrada: mesh_src_agent
//
// Integra sequencer, driver y monitor.
// Propaga el virtual interface hacia sus componentes internos.
// Conecta sequencer con driver durante la fase connect.
// ===============================================================

class mesh_src_agent extends uvm_agent;

  `uvm_component_utils(mesh_src_agent)

  // Interface hacia el DUT
  mesh_vif_t vif;

  // Componentes del agente
  mesh_sequencer    seqr;
  mesh_driver       drv;
  mesh_src_monitor  mon;

  function new(string name = "mesh_src_agent", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  // Construcción del agente y propagación del virtual interface
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Obtiene interface para el agente
    if (!uvm_config_db#(mesh_vif_t)::get(this, "", "vif", vif)) begin
      `uvm_fatal(get_type_name(),
                 "No se pudo obtener el virtual interface 'vif' para mesh_src_agent")
    end

    // Crea los componentes internos
    seqr = mesh_sequencer   ::type_id::create("seqr", this);
    drv  = mesh_driver      ::type_id::create("drv",  this);
    mon  = mesh_src_monitor ::type_id::create("mon",  this);

    // Propaga interface a driver y monitor
    uvm_config_db#(mesh_vif_t)::set(this, "drv", "vif", vif);
    uvm_config_db#(mesh_vif_t)::set(this, "mon", "vif", vif);
  endfunction

  // Conexión entre sequencer y driver
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    drv.seq_item_port.connect(seqr.seq_item_export);
  endfunction

endclass : mesh_src_agent


/////////////////////////////////////////////////////////////////////////////////////////////////////
// ===============================================================
// Sink driver de salida: mesh_sink_driver
//
// Encargado de revisar pndng en todas las terminales y generar pop
// cuando corresponde. Puede trabajar en modo normal o en modo
// especial para pruebas de back-pressure, donde se retarda el pop.
// La configuración se recibe mediante uvm_config_db.
// ===============================================================

class mesh_sink_driver extends uvm_component;

  `uvm_component_utils(mesh_sink_driver)

  mesh_vif_t vif;

  // Número de terminales de salida
  localparam int NTERMS = 16;

  // Control general del drenaje de datos hacia afuera
  bit enable_auto_pop = 1'b1;               // permite consumo automático
  bit [NTERMS-1:0] pop_enable_mask = '1;    // habilita pop por terminal

  // Configuración de modo back-pressure
  bit          backpressure_mode         = 1'b0;
  int unsigned backpressure_hold_cycles  = 0;

  function new(string name = "mesh_sink_driver", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  // Obtiene interface y parámetros desde la config DB
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(mesh_vif_t)::get(this, "", "vif", vif)) begin
      `uvm_fatal(get_type_name(),
                 "No se pudo obtener el virtual interface 'vif' para mesh_sink_driver")
    end

    void'(uvm_config_db#(bit)::get(this, "", "enable_auto_pop", enable_auto_pop));
    void'(uvm_config_db#(bit [NTERMS-1:0])::get(
            this, "", "pop_enable_mask", pop_enable_mask));

    void'(uvm_config_db#(bit)::get(this, "", "backpressure_mode", backpressure_mode));
    void'(uvm_config_db#(int unsigned)::get(
            this, "", "backpressure_hold_cycles", backpressure_hold_cycles));
  endfunction

  // Ejecución del comportamiento de consumo de datos
  virtual task run_phase(uvm_phase phase);
    int t;

    // Inicializa pop en cero
    for (t = 0; t < NTERMS; t++) begin
      vif.pop[t] <= 1'b0;
    end

    // Espera la salida de reset
    @(negedge vif.reset);

    // Modo especial de back-pressure
    if (backpressure_mode) begin

      `uvm_info(get_type_name(),
                $sformatf("Sink driver en modo BACKPRESSURE: hold %0d ciclos sin pop",
                          backpressure_hold_cycles),
                UVM_LOW)

      // Mantiene pop en cero durante los ciclos de retención
      for (int n = 0; n < backpressure_hold_cycles; n++) begin
        @(posedge vif.clk);
        if (vif.reset) begin
          for (t = 0; t < NTERMS; t++) begin
            vif.pop[t] <= 1'b0;
          end
        end
        else begin
          for (t = 0; t < NTERMS; t++) begin
            vif.pop[t] <= 1'b0;
          end
        end
      end

      `uvm_info(get_type_name(),
                "Sink driver: Fase de back-pressure terminada, iniciando drenaje automático",
                UVM_LOW)

      // Comportamiento de drenaje automático después del retardo
      forever begin
        @(posedge vif.clk);

        if (vif.reset) begin
          for (t = 0; t < NTERMS; t++) begin
            vif.pop[t] <= 1'b0;
          end
        end
        else begin
          for (t = 0; t < NTERMS; t++) begin
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

    // Modo normal de operación
    forever begin
      @(posedge vif.clk);

      if (vif.reset) begin
        for (t = 0; t < NTERMS; t++) begin
          vif.pop[t] <= 1'b0;
        end
      end
      else begin
        if (!enable_auto_pop) begin
          // No se drena ninguna FIFO
          for (t = 0; t < NTERMS; t++) begin
            vif.pop[t] <= 1'b0;
          end
        end
        else begin
          // Pop automático por terminal cuando hay pndng
          for (t = 0; t < NTERMS; t++) begin
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
// Detecta cuando se consume un paquete en una terminal t, usando
// pndng y pop. Captura el vector de 40 bits, decodifica sus
// campos y genera un mesh_out_event. El evento se envía al
// scoreboard mediante un analysis_port y también se registra
// en un covergroup para cobertura.
// ===============================================================

class mesh_sink_monitor extends uvm_component;

  `uvm_component_utils(mesh_sink_monitor)

  mesh_vif_t vif;

  // Puerto de análisis hacia el scoreboard
  uvm_analysis_port #(mesh_out_event) ap;

  localparam int NTERMS = 16;

  // Variable para cobertura
  mesh_out_event cov_evt;

  // Covergroup para muestrear eventos de salida
  covergroup cg_sink_h;

    coverpoint cov_evt.dst_term {
      bins all_terms[] = {[0:15]};
    }

    coverpoint cov_evt.dst_row {
      bins dir_vals[] = {[0:5]};
    }
    
    coverpoint cov_evt.dst_col {
      bins dir_vals[] = {[0:5]};
    }

    coverpoint cov_evt.payload;

    coverpoint cov_evt.mode {
      bins row_first = {MESH_MODE_ROW_FIRST};
      bins col_first = {MESH_MODE_COL_FIRST};
    }

    coverpoint cov_evt.nxt_jump {
      bins dir_vals[] = {[0:3]};
    }

  endgroup

  function new(string name = "mesh_sink_monitor", uvm_component parent = null);
    super.new(name, parent);
    ap = new("ap", this);
    cg_sink_h = new();
  endfunction

  // Obtiene el virtual interface desde config DB
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(mesh_vif_t)::get(this, "", "vif", vif)) begin
      `uvm_fatal(get_type_name(),
                 "No se pudo obtener el virtual interface 'vif' para mesh_sink_monitor")
    end
  endfunction

  // Captura de paquetes consumidos
  virtual task run_phase(uvm_phase phase);
    bit [39:0] bits;
    mesh_out_event evt;

    forever begin
      @(posedge vif.clk);

      if (!vif.reset) begin
        for (int t = 0; t < NTERMS; t++) begin

          // Un paquete es consumido cuando pndng y pop están activos
          if (vif.pndng[t] && vif.pop[t]) begin     
            bits = vif.data_out[t];

            evt = mesh_out_event::type_id::create(
                    $sformatf("out_evt_term%0d_time%0t", t, $time), this);

            evt.dst_term  = t;
            evt.recv_time = $time;
            evt.data      = bits;

            evt.nxt_jump = bits[39:32];
            evt.dst_row  = bits[31:28];
            evt.dst_col  = bits[27:24];
            evt.payload  = bits[22:0];

            evt.mode = (bits[23] == 1'b1) ?
                        MESH_MODE_ROW_FIRST : MESH_MODE_COL_FIRST;

            `uvm_info(get_type_name(),
                      $sformatf("Monitor SINK: dst_term=%0d time=%0t bits=%h row=%0d col=%0d mode=%0d payload=0x%0h",
                                evt.dst_term, evt.recv_time, bits,
                                evt.dst_row, evt.dst_col, evt.mode, evt.payload),
                      UVM_LOW)

            // Muestra cobertura
            cov_evt = evt;
            cg_sink_h.sample();

            // Envía evento al scoreboard
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
// Agrupa driver y monitor de salida. Recibe el virtual interface
// mediante config DB y lo pasa a sus componentes internos.
// ===============================================================

class mesh_sink_agent extends uvm_agent;

  `uvm_component_utils(mesh_sink_agent)

  mesh_vif_t vif;

  mesh_sink_driver  drv;
  mesh_sink_monitor mon;

  function new(string name = "mesh_sink_agent", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  // Construcción del agente y propagación del virtual interface
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(mesh_vif_t)::get(this, "", "vif", vif)) begin
      `uvm_fatal(get_type_name(),
                 "No se pudo obtener el virtual interface 'vif' para mesh_sink_agent")
    end

    drv = mesh_sink_driver ::type_id::create("drv", this);
    mon = mesh_sink_monitor::type_id::create("mon", this);

    uvm_config_db#(mesh_vif_t)::set(this, "drv", "vif", vif);
    uvm_config_db#(mesh_vif_t)::set(this, "mon", "vif", vif);
  endfunction

endclass : mesh_sink_agent



endpackage : mesh_uvm_pkg


// Interface que conecta la malla 4x4 con el ambiente UVM.
// Define reloj, reset y todas las señales necesarias entre DUT y testbench.
interface mesh_if #(
  parameter int ROWS   = 4,
  parameter int COLUMS = 4,
  parameter int PCK_W  = 40
);

  // Número total de terminales externas según filas y columnas de la malla
  localparam int NTERMS = ROWS*2 + COLUMS*2;

  // Señales globales de reloj y reset
  logic clk;
  logic reset;

  // Señales generadas por el DUT hacia el exterior
  logic                  pndng      [NTERMS];      // indica dato pendiente para cada terminal
  logic [PCK_W-1:0]      data_out   [NTERMS];      // paquete de 40 bits enviado a cada terminal
  logic                  popin      [NTERMS];      // señal que registra consumo exitoso por parte del DUT

  // Señales desde el exterior hacia el DUT
  logic                  pop        [NTERMS];      // indica al DUT que se consume un dato disponible
  logic [PCK_W-1:0]      data_out_i_in[NTERMS];    // paquete inyectado desde el entorno hacia el DUT
  logic                  pndng_i_in [NTERMS];      // indica al DUT que hay un paquete válido para consumir
  
  // ==========================================================
  // Aserciones de protocolo en la interfaz
  // Estas aserciones verifican estabilidad del dato y validez
  // del handshake entre DUT y exterior durante la simulación.
  // ==========================================================

  genvar t;

  // Aserción de salida (SINK): si hay dato pendiente y no se hace pop,
  // el valor de data_out debe permanecer estable.
  for (t = 0; t < NTERMS; t++) begin : SINK_IF_ASSERTS

    property hold_data_while_pending;
      @(posedge clk) disable iff (reset)
        (pndng[t] && !pop[t]) |=> $stable(data_out[t]);
    endproperty

    assert property (hold_data_while_pending)
      else $error("SINK %0d: data_out cambió mientras pndng=1 y sin pop", t);

  end

  // Aserción de entrada (SRC): popin solo es válido si el entorno
  // presentó un dato válido mediante pndng_i_in.
  for (t = 0; t < NTERMS; t++) begin : SRC_IF_ASSERTS

    property popin_implies_valid;
      @(posedge clk) disable iff (reset)
        popin[t] |-> pndng_i_in[t];
    endproperty

    assert property (popin_implies_valid)
      else $error("SRC %0d: popin sin pndng_i_in (dato válido)", t);

  end

  // Modport para conectar el DUT.
  // El DUT recibe señales del exterior y entrega señales hacia el testbench.
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

  // Modport para conectar el ambiente UVM (drivers y monitores).
  // El testbench observa salidas del DUT y controla señales de entrada.
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
  import mesh_uvm_pkg::*; // Importa tipos usados en la malla

  // ================================================================
  // 1) Clase helper: mesh_expected_pkt
  // Representa un paquete esperado según el modelo de referencia.
  // Almacena los campos necesarios para compararlo con la salida.
  // ================================================================
  class mesh_expected_pkt extends uvm_object;

    `uvm_object_utils(mesh_expected_pkt)

    // Campos básicos del paquete
    int unsigned src_term;
    bit [3:0]    dst_row;
    bit [3:0]    dst_col;
    mesh_mode_e  mode;
    bit [22:0]   payload;

    // Campos completos que deben coincidir con la salida del DUT
    bit [7:0]    nxt_jump;
    bit [39:0]   full_bits;

    // Tiempo en que la entrada fue aceptada
    time         send_time;

    function new(string name = "mesh_expected_pkt");
      super.new(name);
    endfunction

  endclass : mesh_expected_pkt


  // ================================================================
  // 2) Reference model: mesh_ref_model
  // Modela el comportamiento esperado de la malla.
  // Calcula nxt_jump, construye el paquete completo y mantiene
  // una cola de paquetes pendientes por comparar.
  // ================================================================
  class mesh_ref_model extends uvm_object;

    `uvm_object_utils(mesh_ref_model)

    // Cola interna con los paquetes esperados
    protected mesh_expected_pkt expected_q[$];

    function new(string name = "mesh_ref_model");
      super.new(name);
    endfunction

    // Determina el valor nxt_jump según zona destino
    function automatic bit [7:0] calc_nxt_jump(bit [3:0] dst_row,
                                               bit [3:0] dst_col);
      bit [7:0] val;

      // Zona norte
      if (dst_row == 4'd0 && dst_col inside {4'd1,4'd2,4'd3,4'd4})
        val = 8'd0;
      // Zona oeste
      else if (dst_col == 4'd0 && dst_row inside {4'd1,4'd2,4'd3,4'd4})
        val = 8'd3;
      // Zona sur
      else if (dst_row == 4'd5 && dst_col inside {4'd1,4'd2,4'd3,4'd4})
        val = 8'd2;
      // Zona este
      else if (dst_col == 4'd5 && dst_row inside {4'd1,4'd2,4'd3,4'd4})
        val = 8'd1;
      else
        val = 8'hFF;     // Zona fuera del mapa definido

      return val;
    endfunction

    // Construye el paquete completo de 40 bits según el formato lógico
    function automatic bit [39:0] build_full_bits(bit [7:0]   nxt_jump,
                                                  bit [3:0]   dst_row,
                                                  bit [3:0]   dst_col,
                                                  mesh_mode_e mode,
                                                  bit [22:0]  payload);
      bit [39:0] pkt;
      bit        mode_bit;

      // Traducción del enum a un bit
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

    // Recibe un mesh_packet de entrada y lo convierte en un paquete esperado
    virtual function void add_input_tr(mesh_packet in_tr);
      mesh_expected_pkt exp;
      bit [7:0]  loc_nxt;
      bit [39:0] loc_bits;

      loc_nxt = calc_nxt_jump(in_tr.dst_row, in_tr.dst_col);
      
      // Si no hay mapeo, se descarta el paquete
      if (loc_nxt == 8'hFF) begin
        `uvm_warning(get_type_name(),
                     $sformatf("REF: destino no mapeado row=%0d col=%0d, se ignora en expected_q",
                               in_tr.dst_row, in_tr.dst_col))
        return;
      end
      
      // Construye vector completo esperado
      loc_bits = build_full_bits(loc_nxt,
                                 in_tr.dst_row,
                                 in_tr.dst_col,
                                 in_tr.mode,
                                 in_tr.payload);

      // Crea y almacena el paquete esperado
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

    // Compara una salida del DUT con la cola de esperados
    virtual function bit match_output_ev(mesh_out_event out_ev,
                                         output mesh_expected_pkt matched);
      bit found = 0;
      bit [39:0] out_bits;

      out_bits = out_ev.data;

      // Busca coincidencia exacta en full_bits
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

    // Regresa cuántos paquetes siguen en cola sin emparejar
    virtual function int unsigned num_pending();
      return expected_q.size();
    endfunction

    // Reporta todos los paquetes pendientes
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
  // Coordina la comparación entre entradas y salidas.
  // Registra coincidencias y mismatches y genera un archivo CSV.
  // ================================================================

  // Declara analysis_imp diferenciados para entrada y salida
  `uvm_analysis_imp_decl(_in)
  `uvm_analysis_imp_decl(_out)

  class mesh_scoreboard extends uvm_component;

    `uvm_component_utils(mesh_scoreboard)

    // Modelo de referencia
    mesh_ref_model refm;

    // Conexiones desde los monitores
    uvm_analysis_imp_in  #(mesh_packet,    mesh_scoreboard) in_imp;
    uvm_analysis_imp_out #(mesh_out_event, mesh_scoreboard) out_imp;

    // Contadores de resultados
    int unsigned num_matches;
    int unsigned num_mismatches;

    // Manejo de archivo CSV
    int    csv_fd;
    string csv_filename;

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    // Construcción del scoreboard
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      refm  = mesh_ref_model::type_id::create("refm");
      in_imp  = new("in_imp",  this);
      out_imp = new("out_imp", this);

      num_matches    = 0;
      num_mismatches = 0;

      // Apertura del archivo CSV
      csv_filename = "mesh_report.csv";
      csv_fd = $fopen(csv_filename, "w");

      if (csv_fd == 0) begin
        `uvm_error(get_type_name(),
                   $sformatf("No se pudo abrir archivo CSV '%s'", csv_filename))
      end
      else begin
        // Encabezado del archivo CSV
        $fdisplay(csv_fd,
          "send_time,src_term,dst_term,recv_time,delay,mode,payload_hex,nxt_jump,row,col");
      end
    endfunction

    // Recibe entrada desde mesh_src_monitor
    virtual function void write_in(mesh_packet tr);
      `uvm_info(get_type_name(),
                $sformatf("SCB: evento entrada src=%0d row=%0d col=%0d mode=%0d payload=0x%0h t=%0t",
                          tr.src_term, tr.dst_row, tr.dst_col, tr.mode,
                          tr.payload, tr.send_time),
                UVM_LOW)
      refm.add_input_tr(tr);
    endfunction

    // Recibe salida desde mesh_sink_monitor
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

        // Registro CSV para este match
        if (csv_fd != 0) begin
          $fdisplay(csv_fd,
            "%0t,%0d,%0d,%0t,%0t,%0d,0x%0h,0x%0h,%0d,%0d",
            exp.send_time,
            exp.src_term,
            ev.dst_term,
            ev.recv_time,
            delay,
            exp.mode,
            exp.payload,
            exp.nxt_jump,
            exp.dst_row,
            exp.dst_col
          );
        end
      end
      else begin
        num_mismatches++;

        `uvm_error(get_type_name(),
                   $sformatf("SCB: NO MATCH para data=%h en dst_term=%0d t=%0t",
                             ev.data, ev.dst_term, ev.recv_time))
      end
    endfunction

    // Fase final: reporte de paquetes pendientes y cierre del archivo CSV
    int unsigned pending;
    virtual function void final_phase(uvm_phase phase);
      super.final_phase(phase);

      pending = refm.num_pending();

      // Si quedaron paquetes sin salida, contarlos como mismatches
      if (pending != 0) begin
        num_mismatches += pending;

        `uvm_error(get_type_name(),
                   $sformatf("Quedaron %0d paquetes esperados sin recibir.",
                             pending))

        refm.report_pending();
      end

      `uvm_info(get_type_name(),
                $sformatf("SCB final: matches=%0d mismatches=%0d pendientes=%0d",
                          num_matches, num_mismatches, pending),
                UVM_LOW)

      if (csv_fd != 0) begin
        $fclose(csv_fd);
        `uvm_info(get_type_name(),
                  $sformatf("Reporte CSV generado en '%s'", csv_filename),
                  UVM_LOW)
      end
    endfunction

  endclass : mesh_scoreboard



  // ================================================================
  // Entorno UVM: mesh_env
  // Construye agentes y scoreboard y conecta monitores a sus imp.
  // ================================================================
  class mesh_env extends uvm_env;

    `uvm_component_utils(mesh_env)

    // Agentes que inyectan y extraen paquetes del DUT
    mesh_src_agent   src_agent;
    mesh_sink_agent  sink_agent;

    // Scoreboard con modelo de referencia
    mesh_scoreboard  scb;

    function new(string name = "mesh_env", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    // Crea subcomponentes del entorno
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      src_agent  = mesh_src_agent ::type_id::create("src_agent",  this);
      sink_agent = mesh_sink_agent::type_id::create("sink_agent", this);
      scb        = mesh_scoreboard::type_id::create("scb",        this);

      `uvm_info(get_type_name(),
                "mesh_env: build_phase completado",
                UVM_LOW)
    endfunction

    // Conecta analysis_ports con analysis_imp del scoreboard
    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);

      src_agent.mon.ap.connect(scb.in_imp);
      sink_agent.mon.ap.connect(scb.out_imp);

      `uvm_info(get_type_name(),
                "mesh_env: connect_phase completado",
                UVM_LOW)
    endfunction

  endclass : mesh_env

endpackage : mesh_scoreboard_pkg

package mesh_test_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import mesh_uvm_pkg::*;  // Importa ambiente, secuencias y agentes
  import mesh_scoreboard_pkg::*; // Importa scoreboard y modelo de referencia

  // ============================================================
  // 1) Test base: mesh_base_test
  // Actúa como plantilla para los demás tests.
  // Crea el ambiente y deja run_phase vacío para que
  // las clases derivadas controlen la ejecución.
  // ============================================================

  class mesh_base_test extends uvm_test;

    `uvm_component_utils(mesh_base_test)

    // Instancia del ambiente principal
    mesh_env env;

    function new(string name = "mesh_base_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction

    // Crea el ambiente usando el factory
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      env = mesh_env::type_id::create("env", this);
    endfunction

    // No ejecuta secuencias; funciona como punto común para herencia
    virtual task run_phase(uvm_phase phase);
      `uvm_info(get_type_name(),
                "mesh_base_test: run_phase vacio (usar clases derivadas)",
                UVM_LOW)
    endtask

  endclass : mesh_base_test

  // ============================================================
  // 2) Test: Conectividad aleatoria
  // Ejecuta la secuencia mesh_rand_connectivity_seq
  // sobre el sequencer del agente de entrada.
  // ============================================================

  class mesh_rand_connectivity_test extends mesh_base_test;

    `uvm_component_utils(mesh_rand_connectivity_test)

    function new(string name = "mesh_rand_connectivity_test",
                 uvm_component parent = null);
      super.new(name, parent);
    endfunction

    // Inicia la secuencia de conectividad aleatoria
    virtual task run_phase(uvm_phase phase);
      mesh_rand_connectivity_seq seq;

      phase.raise_objection(this, "Iniciando Conectividad aleatoria");

      // Crea la secuencia y la envía al sequencer
      seq = mesh_rand_connectivity_seq::type_id::create("seq", this);
      seq.start(env.src_agent.seqr);

      // Tiempo adicional para permitir drenaje completo
      repeat (100) @(posedge env.src_agent.vif.clk);

      phase.drop_objection(this, "Finalizando Conectividad aleatoria");
    endtask

  endclass : mesh_rand_connectivity_test

  // ============================================================
  // 3) Test: Comparacion de modos de ruta
  // Ejecuta la secuencia mesh_compare_modes_seq.
  // ============================================================

  class mesh_compare_modes_test extends mesh_base_test;

    `uvm_component_utils(mesh_compare_modes_test)

    function new(string name = "mesh_compare_modes_test",
                 uvm_component parent = null);
      super.new(name, parent);
    endfunction

    // Inicia la secuencia de comparación de modos
    virtual task run_phase(uvm_phase phase);
      mesh_compare_modes_seq seq;

      phase.raise_objection(this, "Iniciando Comparacion de modos de ruta");

      seq = mesh_compare_modes_seq::type_id::create("seq", this);
      seq.start(env.src_agent.seqr);

      repeat (100) @(posedge env.src_agent.vif.clk);

      phase.drop_objection(this, "Finalizando Comparacion de modos de ruta");
    endtask

  endclass : mesh_compare_modes_test


  // ============================================================
  // 4) Test: Broadcast desde todas las terminales
  // Lanza mesh_broadcast_all_terms_seq.
  // ============================================================

  class mesh_broadcast_all_terms_test extends mesh_base_test;

    `uvm_component_utils(mesh_broadcast_all_terms_test)

    function new(string name = "mesh_broadcast_all_terms_test",
                 uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
      mesh_broadcast_all_terms_seq seq;

      phase.raise_objection(this, "Iniciando Broadcast");

      seq = mesh_broadcast_all_terms_seq::type_id::create("seq", this);
      seq.start(env.src_agent.seqr);

      repeat (100) @(posedge env.src_agent.vif.clk);

      phase.drop_objection(this, "Finalizando Broadcast");
    endtask

  endclass : mesh_broadcast_all_terms_test


  // ============================================================
  // 5) Test: FIFO llena con back-pressure
  // Habilita modo especial en el sink_driver antes de iniciar.
  // Ejecuta mesh_fifo_full_backpressure_seq.
  // ============================================================

class mesh_fifo_backpressure_test extends mesh_base_test;

  `uvm_component_utils(mesh_fifo_backpressure_test)

  function new(string name = "mesh_fifo_backpressure_test",
               uvm_component parent = null);
    super.new(name, parent);
  endfunction

  // Configuración previa para habilitar backpressure en sink_driver
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Enciende modo backpressure
    uvm_config_db#(bit)::set(null,
                          "uvm_test_top.env.sink_agent.drv",
                          "backpressure_mode",
                          1'b1);

    // Define la cantidad de ciclos sin pop al inicio
    uvm_config_db#(int unsigned)::set(null,
                          "uvm_test_top.env.sink_agent.drv",
                          "backpressure_hold_cycles",
                                      500);  
  endfunction

  // Inicia la secuencia con backpressure
  virtual task run_phase(uvm_phase phase);
    mesh_fifo_full_backpressure_seq seq;

    phase.raise_objection(this, "Iniciando FIFO full + back-pressure");

    seq = mesh_fifo_full_backpressure_seq::type_id::create("seq");
    seq.start(env.src_agent.seqr);

    repeat (100) @(posedge env.src_agent.vif.clk);

    phase.drop_objection(this, "Finalizando FIFO full + back-pressure");
  endtask

endclass : mesh_fifo_backpressure_test


  // ============================================================
  // 6) Test: Contencion fuerte con todos los puertos activos
  // Ejecuta mesh_full_load_contention_seq.
  // ============================================================

  class mesh_full_contention_test extends mesh_base_test;

    `uvm_component_utils(mesh_full_contention_test)

    function new(string name = "mesh_full_contention_test",
                 uvm_component parent = null);
      super.new(name, parent);
    endfunction

    // Inicia secuencia de carga alta
    virtual task run_phase(uvm_phase phase);
      mesh_full_load_contention_seq seq;

      phase.raise_objection(this, "Iniciando Contencion fuerte / full load");

      seq = mesh_full_load_contention_seq::type_id::create("seq", this);
      seq.start(env.src_agent.seqr);

      repeat (100) @(posedge env.src_agent.vif.clk);

      phase.drop_objection(this, "Finalizando Contencion fuerte / full load");
    endtask

  endclass : mesh_full_contention_test


  // ============================================================
  // 7) Test: Arbitraje moderado hacia un mismo destino
  // Ejecuta mesh_moderate_arbitration_seq.
  // ============================================================

  class mesh_moderate_arbitration_test extends mesh_base_test;

    `uvm_component_utils(mesh_moderate_arbitration_test)

    function new(string name = "mesh_moderate_arbitration_test",
                 uvm_component parent = null);
      super.new(name, parent);
    endfunction

    // Inicia secuencia de arbitraje moderado
    virtual task run_phase(uvm_phase phase);
      mesh_moderate_arbitration_seq seq;

      phase.raise_objection(this, "Iniciando Arbitraje moderado a un destino");

      seq = mesh_moderate_arbitration_seq::type_id::create("seq", this);
      seq.start(env.src_agent.seqr);

      repeat (100) @(posedge env.src_agent.vif.clk);

      phase.drop_objection(this, "Finalizando Arbitraje moderado a un destino");
    endtask

  endclass : mesh_moderate_arbitration_test


  // ============================================================
  // 8) Test: Router como terminal y destino (self-loop)
  // Ejecuta mesh_self_loopback_seq.
  // ============================================================

  class mesh_selfloop_test extends mesh_base_test;

    `uvm_component_utils(mesh_selfloop_test)

    function new(string name = "mesh_selfloop_test",
                 uvm_component parent = null);
      super.new(name, parent);
    endfunction

    // Inicia la secuencia de auto consumo
    virtual task run_phase(uvm_phase phase);
      mesh_self_loopback_seq seq;

      phase.raise_objection(this, "Iniciando Router como terminal y destino");

      seq = mesh_self_loopback_seq::type_id::create("seq", this);
      seq.start(env.src_agent.seqr);

      repeat (100) @(posedge env.src_agent.vif.clk);

      phase.drop_objection(this, "Finalizando Router como terminal y destino");
    endtask

  endclass : mesh_selfloop_test


  // ============================================================
  // 9) Test: Casos invalidos de External ID
  // Ejecuta mesh_invalid_external_id_seq.
  // ============================================================

  class mesh_invalid_external_id_test extends mesh_base_test;

    `uvm_component_utils(mesh_invalid_external_id_test)

    function new(string name = "mesh_invalid_external_id_test",
                 uvm_component parent = null);
      super.new(name, parent);
    endfunction

    // Inicia la secuencia con destinos no válidos
    virtual task run_phase(uvm_phase phase);
      mesh_invalid_external_id_seq seq;

      phase.raise_objection(this, "Iniciando prueba casos invalidos");

      seq = mesh_invalid_external_id_seq::type_id::create("seq", this);
      seq.start(env.src_agent.seqr);

      repeat (100) @(posedge env.src_agent.vif.clk);

      phase.drop_objection(this, "Finalizando prueba casos invalidos");
    endtask

  endclass : mesh_invalid_external_id_test

endpackage : mesh_test_pkg

/////////////////////////////////////////////////////////////////////////////////////////////////////

// Top-level testbench para la malla 4x4 con UVM.
// Define la estructura principal del banco de pruebas:
// - Crea la interface mesh_if que conecta el DUT con UVM.
// - Instancia el DUT con sus puertos enlazados a la interface.
// - Genera reloj y reset para todo el sistema.
// - Coloca el virtual interface en la config_db para que UVM lo recupere.
// - Llama a run_test(), permitiendo seleccionar el test mediante +UVM_TESTNAME.

import uvm_pkg::*;
`include "uvm_macros.svh"

// Importa paquetes que contienen ambiente, agentes, secuencias y scoreboard
import mesh_uvm_pkg::*;
import mesh_scoreboard_pkg::*;
import mesh_test_pkg::*;  // Contiene los tests derivados

module mesh_top_tb;

  // Parámetros que definen el tamaño de la malla y el ancho del paquete
  localparam int ROWS   = 4;
  localparam int COLUMS = 4;
  localparam int PCK_W  = 40;

  // Instancia de la interface que declara todas las señales usadas por el DUT
  mesh_if #(
    .ROWS   (ROWS),
    .COLUMS (COLUMS),
    .PCK_W  (PCK_W)
  ) mesh_if_inst();

  // Instancia del DUT
  mesh_gnrtr #(
    .ROWS    (ROWS),
    .COLUMS  (COLUMS),
    .pckg_sz (PCK_W)
  ) dut (
    .pndng        (mesh_if_inst.pndng),        // Salida indicando dato disponible
    .data_out     (mesh_if_inst.data_out),     // Salida de datos desde la malla
    .popin        (mesh_if_inst.popin),        // Señal que indica consumo por parte del DUT
    .pop          (mesh_if_inst.pop),          // Señal de extracción generada por el entorno
    .data_out_i_in(mesh_if_inst.data_out_i_in),// Datos inyectados externamente al DUT
    .pndng_i_in   (mesh_if_inst.pndng_i_in),   // Señal que indica disponibilidad de dato externo
    .clk          (mesh_if_inst.clk),          // Reloj principal
    .reset        (mesh_if_inst.reset)         // Reset para inicialización del DUT
  );


  // Generación de reloj y reset

  // Genera un reloj continuo con periodo de 10 ns
  initial begin
    mesh_if_inst.clk = 0;
    forever #5 mesh_if_inst.clk = ~mesh_if_inst.clk;
  end

  // Genera un reset activo por algunos ciclos de reloj
  initial begin
    mesh_if_inst.reset = 1'b1;
    repeat (5) @(posedge mesh_if_inst.clk);
    mesh_if_inst.reset = 1'b0;
  end

  initial begin
    // Inserta mesh_if_inst en la base de configuración UVM
    uvm_config_db#(mesh_vif_t)::set(null, "*", "vif", mesh_if_inst);

    // Desactiva timeout global y arranca UVM
    uvm_root::get().set_timeout(0, 0);
    run_test();  // Utiliza el test seleccionado
  end

endmodule : mesh_top_tb





 
