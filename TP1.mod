/*********************************************************
 * OPL 12.8.0.0 Model
 * 71.14 - Modelos y Optimizacion I - 1c2019 - TP1
 * Author: El Grupo
 *  79979 - Gonzalez, Juan Manuel (juanmg0511@gmail.com)
 *  86578 - Fanego, Christian (christian.fanego@gmail.com)
 *  96356 - Botalla, Tomas (tbotalla@hotmail.com)
 * Creation Date: 5/5/2019 at 13:09:30
 *********************************************************/

// Asociacion con los datos
// Conjunto de productos
{int} PRODUCTOS = ...;

// Constantes con disponibilidad, precios y preferencias
int DISPONIBILIDAD[PRODUCTOS] = ...;
int PRECIO_PROMO[PRODUCTOS] = ...;
int PRECIO_REGULAR[PRODUCTOS] = ...;
int PREFERENCIAS_PROMO[PRODUCTOS] = ...;
int PREFERENCIAS_REGULAR[PRODUCTOS] = ...;

// Modelo
// Constante M para las restricciones
float M = 1000000;

// Variables de decision 
// Productos que lleva el usuario, en precio promocion y regular
dvar boolean Y_P[PRODUCTOS]; // 1: el usuario lleva el producto i a precio promocional - 0: si no
dvar boolean Y_R[PRODUCTOS]; // 1: el usuario lleva el producto i a precio regular - 0: si no

// Condiciones de promocion
// I - El cliente prefiere el producto en promo por sobre el resto de los productos disponibles a precio regular
dvar boolean Y_PREF_P_ANTES_R[PRODUCTOS][PRODUCTOS];
dvar boolean Y_PREF_P_ANTES_R_DISPO[PRODUCTOS][PRODUCTOS];
dvar boolean Y_PREF_P_ANTES_R_RESTO[PRODUCTOS];

// II - El producto en promo genera mas ingresos al super que el resto de los productos disponibles a precio regular
dvar int+ PREF_PREFERIDO_REGULAR[PRODUCTOS];
dvar int+ PRECIO_PREFERIDO_REGULAR[PRODUCTOS];
dvar int+ PREF_PROMO_EN_PROMO[PRODUCTOS];
dvar int+ PRECIO_PROMO_EN_PROMO[PRODUCTOS];
dvar int+ VALOR_PRECIO_PREFERIDO_REGULAR;
dvar int+ VALOR_PREF_PREFERIDO_REGULAR;
dvar boolean Y_PREF_POSIBLES_PROMO_MEJOR_PREFERIDO_REGULAR[PRODUCTOS];
dvar boolean Y_PRECIO_POSIBLES_PROMO_MEJOR_PREFERIDO_REGULAR[PRODUCTOS];

// Indican si se envia una promocion por producto y en general
dvar boolean Y_HAY_PROMO_PROD[PRODUCTOS];
dvar boolean Y_HAY_PROMO_GENE;

// Indican cual es el producto disponible mas preferido por el usuario, a precio regular 
dvar boolean Y_PREF_I_ANTES_J[PRODUCTOS][PRODUCTOS];
dvar boolean Y_PREF_I_ANTES_J_DISPO[PRODUCTOS][PRODUCTOS];
dvar boolean Y_PREF_I_ANTES_J_RESTO[PRODUCTOS];

// Funcional
maximize
  sum(i in PRODUCTOS) (Y_P[i] * PRECIO_PROMO[i] + Y_R[i] * PRECIO_REGULAR[i]);
 
// Restricciones 
subject to {

  // Condiciones de promo I
  // Comparacion de todos contra todos, con i distinto a j
  preferencia_producto_regular_vs_promo_todos_contra_todos_disponibilidad:
  forall(i in PRODUCTOS) { 
    forall(j in PRODUCTOS:i!=j) {

        PREFERENCIAS_REGULAR[i] - PREFERENCIAS_PROMO[j] >= -M * (1 - Y_PREF_P_ANTES_R[i][j]);
        PREFERENCIAS_REGULAR[i] - PREFERENCIAS_PROMO[j] <=  M * Y_PREF_P_ANTES_R[i][j];
        
        // Disponibilidad
        Y_PREF_P_ANTES_R_DISPO[i][j] ==  Y_PREF_P_ANTES_R[i][j] * DISPONIBILIDAD[i] * DISPONIBILIDAD[j];
    }
  }
  // Comparacion de un producto contra el resto
  preferencia_producto_regular_vs_promo_uno_contra_el_resto:  
  forall(i in PRODUCTOS) { 
  
    sum(j in PRODUCTOS:i!=j) (Y_PREF_P_ANTES_R_DISPO[j][i]) >= (sum(k in PRODUCTOS) (DISPONIBILIDAD[k]) - 1) * Y_PREF_P_ANTES_R_RESTO[i];
    sum(j in PRODUCTOS:i!=j) (Y_PREF_P_ANTES_R_DISPO[j][i]) <= (sum(k in PRODUCTOS) (DISPONIBILIDAD[k]) - 1 - 1) + Y_PREF_P_ANTES_R_RESTO[i];
  }
    
  // Condiciones de promo II
  // Determinacion de los datos sobre los que se calculara la condicion, vinculacion con la condicion I
  datos_condicion_ii:
  forall(i in PRODUCTOS) {

    PREF_PREFERIDO_REGULAR[i] == Y_PREF_I_ANTES_J_RESTO[i] * PREFERENCIAS_REGULAR[i];  
    PRECIO_PREFERIDO_REGULAR[i] == Y_PREF_I_ANTES_J_RESTO[i] * PRECIO_REGULAR[i];

    PREF_PROMO_EN_PROMO[i] <= M + M * Y_PREF_P_ANTES_R_RESTO[i];
    PREF_PROMO_EN_PROMO[i] >= M - M * Y_PREF_P_ANTES_R_RESTO[i];
    PREF_PROMO_EN_PROMO[i] <= PREFERENCIAS_PROMO[i] + M * (1 - Y_PREF_P_ANTES_R_RESTO[i]);
    PREF_PROMO_EN_PROMO[i] >= PREFERENCIAS_PROMO[i] - M * (1 - Y_PREF_P_ANTES_R_RESTO[i]);

    PRECIO_PROMO_EN_PROMO[i] == Y_PREF_P_ANTES_R_RESTO[i] * PRECIO_PROMO[i];
  }
  // Preferencia del producto preferido a precio regular
  valor_pref_producto_regular:
  VALOR_PREF_PREFERIDO_REGULAR == sum(i in PRODUCTOS) (PREF_PREFERIDO_REGULAR[i]);
  // Precio del producto preferido a precio regular
  precio_pref_producto_regular:
  VALOR_PRECIO_PREFERIDO_REGULAR == sum(i in PRODUCTOS) (PRECIO_PREFERIDO_REGULAR[i]);
  // Determinacion de los productos en promo que son preferidos por sobre el preferido a precio regular, y si su precio de venta es mayor
  productos_en_promo_mejor_preferido_regular:
  forall(i in PRODUCTOS) {

     VALOR_PREF_PREFERIDO_REGULAR - PREF_PROMO_EN_PROMO[i] >= -M * (1 - Y_PREF_POSIBLES_PROMO_MEJOR_PREFERIDO_REGULAR[i]);
     VALOR_PREF_PREFERIDO_REGULAR - PREF_PROMO_EN_PROMO[i] <=  M * Y_PREF_POSIBLES_PROMO_MEJOR_PREFERIDO_REGULAR[i];
     PRECIO_PROMO_EN_PROMO[i] - VALOR_PRECIO_PREFERIDO_REGULAR >= -M * (1 - Y_PRECIO_POSIBLES_PROMO_MEJOR_PREFERIDO_REGULAR[i]);
     PRECIO_PROMO_EN_PROMO[i] - VALOR_PRECIO_PREFERIDO_REGULAR <=  M * Y_PRECIO_POSIBLES_PROMO_MEJOR_PREFERIDO_REGULAR[i];
  }    
    
  // AND para determinar si hay promocion o no (cumplen I y II), por producto
  hay_promo_producto_and:
  forall(i in PRODUCTOS) { 
   
    Y_PREF_POSIBLES_PROMO_MEJOR_PREFERIDO_REGULAR[i] + Y_PRECIO_POSIBLES_PROMO_MEJOR_PREFERIDO_REGULAR[i] <= 1 + Y_HAY_PROMO_PROD[i];
    Y_PREF_POSIBLES_PROMO_MEJOR_PREFERIDO_REGULAR[i] + Y_PRECIO_POSIBLES_PROMO_MEJOR_PREFERIDO_REGULAR[i] >= 2 * Y_HAY_PROMO_PROD[i]; 
  }
  
  // OR de lo anterior para determinar si hay promocion en general
  hay_promo_producto_general1:
  sum(i in PRODUCTOS) (Y_HAY_PROMO_PROD[i]) <= card(PRODUCTOS) * Y_HAY_PROMO_GENE;
  hay_promo_producto_general2:
  sum(i in PRODUCTOS) (Y_HAY_PROMO_PROD[i]) >= Y_HAY_PROMO_GENE;

  // Condicion de preferencia de producto a precio regular
  // Comparacion de todos contra todos, con i distinto a j
  preferencia_producto_precio_regular_todos_contra_todos_disponibilidad:
  forall(i in PRODUCTOS) { 
    forall(j in PRODUCTOS:i!=j) {
        
        PREFERENCIAS_REGULAR[i] - PREFERENCIAS_REGULAR[j] >= -M * (1 - Y_PREF_I_ANTES_J[i][j]);
        PREFERENCIAS_REGULAR[i] - PREFERENCIAS_REGULAR[j] <=  M * Y_PREF_I_ANTES_J[i][j];
        
        // Disponibilidad
        Y_PREF_I_ANTES_J_DISPO[i][j] ==  Y_PREF_I_ANTES_J[i][j] * DISPONIBILIDAD[i] * DISPONIBILIDAD[j];
    }
  }
  // Comparacion de un producto contra el resto
  preferencia_producto_precio_regular_uno_contra_el_resto:
  forall(i in PRODUCTOS) { 
  
    sum(j in PRODUCTOS:i!=j) (Y_PREF_I_ANTES_J_DISPO[j][i]) >= (sum(k in PRODUCTOS) (DISPONIBILIDAD[k]) - 1) * Y_PREF_I_ANTES_J_RESTO[i];
    sum(j in PRODUCTOS:i!=j) (Y_PREF_I_ANTES_J_DISPO[j][i]) <= (sum(k in PRODUCTOS) (DISPONIBILIDAD[k]) - 1 - 1) + Y_PREF_I_ANTES_J_RESTO[i];
  }
  // El resultado debe ser un solo producto
  total_productos_preferidos_precio_regular:
  sum(i in PRODUCTOS) (Y_PREF_I_ANTES_J_RESTO[i]) == 1;  

  // Vinculacion entre las variables de promocion y preferencia y las del funcional
  hay_promo_producto_final: 
  forall(i in PRODUCTOS) { 
  
    // Si hay promo, para los valores posibles (!=0), dejamos las variables libres y el funcional elegira la de mayor precio
    Y_P[i] <= Y_HAY_PROMO_PROD[i]; 
  }  
  no_hay_promo_producto_final:
  forall(i in PRODUCTOS) { 
  
    Y_R[i] <= -M * (Y_HAY_PROMO_GENE - 1);
    Y_R[i] >= Y_PREF_I_ANTES_J_RESTO[i] - M * (Y_HAY_PROMO_GENE);
    Y_R[i] <= Y_HAY_PROMO_GENE + Y_PREF_I_ANTES_J_RESTO[i];
  }

  // El cliente lleva un solo producto
  total_productos_a_llevar:
  sum(i in PRODUCTOS) (Y_P[i] + Y_R[i]) == 1;
}
