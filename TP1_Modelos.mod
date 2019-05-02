/*********************************************
 * OPL 12.8.0.0 Model
 * Author: root
 * Creation Date: 1/5/2019 at 20:03:00
 *********************************************/

// Asociacion con los datos
{int} PRODUCTOS = ...; // Esto es un conjunto
int DISPONIBILIDAD[PRODUCTOS] = ...; // Es bivalente
int PRECIO_PROMO[PRODUCTOS] = ...;
int PRECIO_REGULAR[PRODUCTOS] = ...;
int PREFERENCIAS_PROMO[PRODUCTOS] = ...;
int PREFERENCIAS_REGULAR[PRODUCTOS] = ...;

// Variables de decision


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


