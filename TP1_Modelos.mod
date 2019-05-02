/*********************************************
 * OPL 12.8.0.0 Model
 * Author: tbotalla
 * Creation Date: 1/5/2019 at 20:03:00
 *********************************************/

// Asociacion con los datos
{int} PRODUCTOS = ...; // Esto es un conjunto
int DISPONIBILIDAD[PRODUCTOS] = ...; // Es bivalente. Ver que no deja con boolean
int PRECIO_PROMO[PRODUCTOS] = ...;
int PRECIO_REGULAR[PRODUCTOS] = ...;
int PREFERENCIAS_PROMO[PRODUCTOS] = ...;
int PREFERENCIAS_REGULAR[PRODUCTOS] = ...;
int M = 10000;
float m = 0.00001;

// Variables de decision
int Y_PREFIERE_PROMO_ANTES_Q_REGULAR[PRODUCTOS, PRODUCTOS] = ...;
dvar int Y_PREFIERE_PROMO_ANTES_Q_RESTO; // TODO: pendiente restringir

// Objetivo
// ...

// Modelo
subject to {

// Restricciones para bivalentes que indican para cada todos los productos
// si prefiere lo prefiere en promo antes que a precio regular 
forall(p in PRODUCTOS) {
	forall(q in PRODUCTOS) {
		preferenciasPromoAntesQueRegular: 
			-M * Y_PREFIERE_PROMO_ANTES_Q_REGULAR[p, q] <= 
			PREFERENCIAS_REGULAR[p] - PREFERENCIAS_PROMO[q]
			<= M * Y_PREFIERE_PROMO_ANTES_Q_REGULAR[p, q];
	}	
}

}

// Restricciones para bivalentes que indican para cada producto si prefiere
// ese producto en promo antes que todos los demas a precio regular
// TODO


// Ejemplo:
/*
{string} PRODUCTOS = ...;
float PRECIO[PRODUCTOS] = ...;
{string} RECURSOS = ...;
int DISPONIBILIDAD[RECURSOS] = ...;
float CONSUMO[RECURSOS, PRODUCTOS] = ...;
{string} CON_DEMANDA_MINIMA = ...;
{string} CON_DEMANDA_MAXIMA = ...;
int DEMANDA_MINIMA[CON_DEMANDA_MINIMA] = ...;
int DEMANDA_MAXIMA[CON_DEMANDA_MAXIMA] = ...;
//Variables continuas positivas
dvar float+ Produccion[PRODUCTOS];
//objetivo
maximize
sum(p in PRODUCTOS) Produccion[p] * PRECIO[p];
//modelo
subject to {
forall(r in RECURSOS) {
recursos: sum(p in PRODUCTOS) Produccion[p] *
CONSUMO[r,p] <= DISPONIBILIDAD[r];
}
forall(p in CON_DEMANDA_MINIMA) {
demandasMinimas: Produccion[p] >= DEMANDA_MINIMA[p];
}
forall(p in CON_DEMANDA_MAXIMA) {
demandasMaximas: Produccion[p] <= DEMANDA_MAXIMA[p];
}
}
*/


