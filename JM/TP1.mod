/*********************************************
 * OPL 12.8.0.0 Model
 * Author: JuanManuelGonzalez
 * Creation Date: 5/5/2019 at 13:09:30
 *********************************************/

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
dvar boolean Y_P[PRODUCTOS];
dvar boolean Y_R[PRODUCTOS];

// Condiciones de promocion
// I - El cliente prefiere el producto en promo por sobre el resto de los productos disponibles a precio regular
dvar boolean Y_PREF_P_ANTES_R[PRODUCTOS][PRODUCTOS];
dvar boolean Y_PREF_P_ANTES_R_DISPO[PRODUCTOS][PRODUCTOS];
dvar boolean Y_PREF_P_ANTES_R_RESTO[PRODUCTOS];
// II - El producto en promo genera mas ingresos al super que el resto de los productos disponibles a precio regular
dvar boolean Y_PRECIO_P_ANTES_R[PRODUCTOS][PRODUCTOS];
dvar boolean Y_PRECIO_P_ANTES_R_DISPO[PRODUCTOS][PRODUCTOS];
dvar boolean Y_PRECIO_P_ANTES_R_RESTO[PRODUCTOS];
// Indican de si se envia una promocion por producto y en general
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

  // Condicion de promo I
  // Comparacion de todos contra todos, con i distinto a j
  forall(i in PRODUCTOS) { 
    forall(j in PRODUCTOS) {
      if (i != j) {
        
        PREFERENCIAS_REGULAR[j] - PREFERENCIAS_PROMO[i] >= -M * (1 - Y_PREF_P_ANTES_R[i][j]);
        PREFERENCIAS_REGULAR[j] - PREFERENCIAS_PROMO[i] <=  M * Y_PREF_P_ANTES_R[i][j];
        
        // Disponibilidad
        Y_PREF_P_ANTES_R_DISPO[i][j] ==  Y_PREF_P_ANTES_R[i][j] * DISPONIBILIDAD[i] * DISPONIBILIDAD[j];
      }
    }
  }
  // Comparacion de 1 producto contra el resto
  forall(i in PRODUCTOS) { 
  
    sum(j in PRODUCTOS:i!=j) (Y_PREF_P_ANTES_R_DISPO[j][i]) >= (sum(k in PRODUCTOS) (DISPONIBILIDAD[k]) - 1) * Y_PREF_P_ANTES_R_RESTO[i];
    sum(j in PRODUCTOS:i!=j) (Y_PREF_P_ANTES_R_DISPO[j][i]) <= (sum(k in PRODUCTOS) (DISPONIBILIDAD[k]) - 1 - 1) + Y_PREF_P_ANTES_R_RESTO[i];
  }
    
  // Condicion de promo II
  // Comparacion de todos contra todos, con i distinto a j
  forall(i in PRODUCTOS) { 
    forall(j in PRODUCTOS) {
      if (i != j) {
        
        PRECIO_PROMO[j] - PRECIO_REGULAR[i] >= -M * (1 - Y_PRECIO_P_ANTES_R[i][j]);
        PRECIO_PROMO[j] - PRECIO_REGULAR[i] <=  M * Y_PRECIO_P_ANTES_R[i][j];
        
        // Disponibilidad
        Y_PRECIO_P_ANTES_R_DISPO[i][j] ==  Y_PRECIO_P_ANTES_R[i][j] * DISPONIBILIDAD[i] * DISPONIBILIDAD[j];
      }
    }
  }
  // Comparacion de 1 producto contra el resto
  forall(i in PRODUCTOS) { 
  
    sum(j in PRODUCTOS:i!=j) (Y_PRECIO_P_ANTES_R_DISPO[j][i]) >= (sum(k in PRODUCTOS) (DISPONIBILIDAD[k]) - 1) * Y_PRECIO_P_ANTES_R_RESTO[i];
    sum(j in PRODUCTOS:i!=j) (Y_PRECIO_P_ANTES_R_DISPO[j][i]) <= (sum(k in PRODUCTOS) (DISPONIBILIDAD[k]) - 1 - 1) + Y_PRECIO_P_ANTES_R_RESTO[i];
  }

  // AND de I y II para determinar si hay promocion o no, por producto
  forall(i in PRODUCTOS) { 
   
    Y_PREF_P_ANTES_R_RESTO[i] + Y_PRECIO_P_ANTES_R_RESTO[i] <= 1 + Y_HAY_PROMO_PROD[i];
    Y_PREF_P_ANTES_R_RESTO[i] + Y_PRECIO_P_ANTES_R_RESTO[i] >= 2 * Y_HAY_PROMO_PROD[i]; 
  }
  
  // OR de lo anterior para determinar si hay promocion en general
  sum(i in PRODUCTOS) (Y_HAY_PROMO_PROD[i]) <= card(PRODUCTOS) * Y_HAY_PROMO_GENE;
  sum(i in PRODUCTOS) (Y_HAY_PROMO_PROD[i]) >= Y_HAY_PROMO_GENE;

  // Condicion de preferencia de producto a precio regular
  // Comparacion de todos contra todos, con i distinto a j
  forall(i in PRODUCTOS) { 
    forall(j in PRODUCTOS) {
      if (i != j) {
        
        PREFERENCIAS_REGULAR[i] - PREFERENCIAS_REGULAR[j] >= -M * (1 - Y_PREF_I_ANTES_J[i][j]);
        PREFERENCIAS_REGULAR[i] - PREFERENCIAS_REGULAR[j] <=  M * Y_PREF_I_ANTES_J[i][j];
        
        // Disponibilidad
        Y_PREF_I_ANTES_J_DISPO[i][j] ==  Y_PREF_I_ANTES_J[i][j] * DISPONIBILIDAD[i] * DISPONIBILIDAD[j];
      }
    }
  }
  // Comparacion de 1 producto contra el resto
  forall(i in PRODUCTOS) { 
  
    sum(j in PRODUCTOS:i!=j) (Y_PREF_I_ANTES_J_DISPO[j][i]) >= (sum(k in PRODUCTOS) (DISPONIBILIDAD[k]) - 1) * Y_PREF_I_ANTES_J_RESTO[i];
    sum(j in PRODUCTOS:i!=j) (Y_PREF_I_ANTES_J_DISPO[j][i]) <= (sum(k in PRODUCTOS) (DISPONIBILIDAD[k]) - 1 - 1) + Y_PREF_I_ANTES_J_RESTO[i];
  }

  // Vinculacion entre las variables de promocion y preferencia y las del funcional
  forall(i in PRODUCTOS) { 
  
    Y_P[i] == Y_HAY_PROMO_PROD[i]; 
  }  
  forall(i in PRODUCTOS) { 
  
    Y_R[i] <= -M * (Y_HAY_PROMO_GENE - 1);
    //Y_R[i] <= Y_PREF_I_ANTES_J_RESTO[i] - M * (Y_HAY_PROMO_GENE);
  }

  // El cliente lleva un solo producto
  sum(i in PRODUCTOS) (Y_P[i] + Y_R[i]) == 1;
}
