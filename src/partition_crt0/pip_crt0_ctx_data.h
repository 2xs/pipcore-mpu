#ifndef __PIP_CRT0_CONTEXT_DATA_H__
#define __PIP_CRT0_CONTEXT_DATA_H__

typedef struct pip_crt0_ctx_data_s {

	/*!
	 * \brief The ID of the block containing the
	 *        partition descriptor of the root
	 *        partition.
	 */
	void *partDescBlockId;

	/*!
	 * \brief The limit address of the stack of
	 *        the root partition.
	 */
	void *stackLimit;

	/*!
	 * \brief The stack top address of the root
	 *        partition.
	 */
	void *stackTop;

	/*!
	 * \brief The VIDT start address of the root
	 *        partition.
	 */
	void *vidtStart;

	/*!
	 * \brief The VIDT end address of the root
	 *        partition.
	 */
	void *vidtEnd;

	/*!
	 * \brief The start address of the root
	 *        partition binary.
	 */
	void *root;
} pip_crt0_ctx_data_t;

#endif /* __PIP_CRT0_CONTEXT_DATA_H__ */
