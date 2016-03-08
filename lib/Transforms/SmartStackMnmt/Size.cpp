#include "llvm/IR/Type.h"
#include "llvm/IR/DerivedTypes.h"

using namespace llvm;

size_t getSizeOf(Type *ty) {
    size_t size = 0;

    if (ty->isIntegerTy())
	size = ty->getIntegerBitWidth() / 8;
    else if (ty->isArrayTy()) {
	ArrayType * arr_ty = cast<ArrayType> (ty);
	size = arr_ty->getNumElements() * arr_ty->getElementType()->getIntegerBitWidth() / 8;
    } else if (ty->isVectorTy()) {
	VectorType * vec_ty = cast<VectorType> (ty);
	size = vec_ty->getNumElements() * vec_ty->getElementType()->getIntegerBitWidth() / 8;
    }
    return size;
}
