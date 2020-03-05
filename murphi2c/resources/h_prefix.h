#pragma once

/* this code was generated by Murphi2C */


#ifdef __cplusplus
extern "C" {
#endif


/* The following function pointers are invoked when model conditions are hit.
 * They have default implementations in generated code, but the default
 * implementation may not be the behaviour you desire in simulation. If this is
 * the case, reassign these to functions implementing your desired behaviour
 * prior to beginning simulation. You can reassign any or all of these as you
 * wish.
 */

/* Called when a model assertion is violated. The default implementation prints
 * the failure message to stderr and then exits.
 */
extern void (*failed_assertion)(const char *message);

/* Called when a model assumption is violated. The default implementation prints
 * the failure message to stderr and then exits.
 */
extern void (*failed_assumption)(const char *message);

/* Called when a model cover property is hit. The default implementation does
 * nothing.
 */
extern void (*cover)(const char *message);

/* Called when a model liveness property is hit. The default implementation does
 * nothing.
 */
extern void (*liveness)(const char *mesage);
