/*
** Copyright (C) 2015 Martin Brain
** 
** This program is free software: you can redistribute it and/or modify
** it under the terms of the GNU General Public License as published by
** the Free Software Foundation, either version 3 of the License, or
** (at your option) any later version.
** 
** This program is distributed in the hope that it will be useful,
** but WITHOUT ANY WARRANTY; without even the implied warranty of
** MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
** GNU General Public License for more details.
** 
** You should have received a copy of the GNU General Public License
** along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

/*
** cvc4_symbolic.h
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 03/06/14
**
** A back-end for symfpu that builds CVC4 nodes rather than executing the
** code directly.  This allows the symfpu code to be used to generate 
** encodings of floating-point operations.
**
*/

#include <stdint.h>

// Symfpu headers
#include "symfpu/utils/properties.h"
#include "symfpu/core/ite.h"
#include "symfpu/core/nondet.h"

#include "util/floatingpoint.h"   // cvc4_literal needs this but can't include it or it will create a loop
#include "symfpu/baseTypes/cvc4_literal.h"


// CVC4 headers
#include "expr/node.h"
#include "expr/type.h"
#include "expr/node_builder.h"
#include "util/bitvector.h"
#include "util/cvc4_assert.h"

#ifndef SYMFPU_CVC4_SYMBOLIC
#define SYMFPU_CVC4_SYMBOLIC


namespace symfpu {
  namespace cvc4_symbolic {


    // Internal versions -- for use in this namespace only
    void iprecondition (const bool b);
    void ipostcondition (const bool b);
    void iinvariant (const bool b);


    typedef unsigned bitWidthType;


    typedef ::CVC4::Node Node;
    typedef ::CVC4::TNode TNode;

    class nodeWrapper {
    protected :
      // TODO : move to inheriting from Node rather than including it
      Node node;

      nodeWrapper (const Node n) : node(n) {}
      nodeWrapper (const nodeWrapper &old) : node(old.node) {}

    public :
      const Node getNode (void) const {
	return this->node;
      }

      Node getNode (void) {
	return this->node;
      }

    };


    class proposition : public nodeWrapper {
    protected :
      bool checkNodeType (const TNode node) {
	::CVC4::TypeNode tn = node.getType(false);
	return tn.isBoolean();
      }

      friend ite<proposition, proposition>;   // For ITE

    public : 
      proposition (const Node n) : nodeWrapper(n) { IPRECONDITION(checkNodeType(node)); }        // Only used within this header so could be friend'd
      proposition (bool v) : nodeWrapper(::CVC4::NodeManager::currentNM()->mkConst(v)) { IPRECONDITION(checkNodeType(node)); }
      proposition (const proposition &old) : nodeWrapper(old) { IPRECONDITION(checkNodeType(node)); }
      proposition (const nonDetMarkerType &)
	: nodeWrapper(::CVC4::NodeManager::currentNM()->mkSkolem("nondet_proposition", 
								 ::CVC4::NodeManager::currentNM()->booleanType(),
								 "created by symfpu")) {  IPRECONDITION(checkNodeType(node)); }

      proposition operator ! (void) const {
	return proposition(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::NOT, this->node));
      }

      proposition operator && (const proposition &op) const {
	return proposition(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::AND, this->node, op.node));
      }

      proposition operator || (const proposition &op) const {
	return proposition(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::OR, this->node, op.node));
      }

      proposition operator == (const proposition &op) const {
	return proposition(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::IFF, this->node, op.node));
      }

      proposition operator ^ (const proposition &op) const {
	return proposition(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::XOR, this->node, op.node));
      }

    };


    // Currently support 5 rounding modes
    #define NUMRM 5

    class roundingMode : public nodeWrapper {
    protected :
      bool checkNodeType (const TNode n) {
	::CVC4::TypeNode tn = n.getType(false);

	return tn.isBitVector(NUMRM);
      }

      // TODO : make this private again
    public :
      roundingMode (const Node n) : nodeWrapper(n) {  IPRECONDITION(checkNodeType(node)); }

      friend ite<proposition, roundingMode>;   // For ITE

    public :
      roundingMode (const unsigned v) : nodeWrapper(::CVC4::NodeManager::currentNM()->mkConst(::CVC4::BitVector(5, v))) {
	IPRECONDITION((v & v-1) == 0 && v != 0);   // Exactly one bit set
	IPRECONDITION(checkNodeType(node));
     }
      roundingMode (const roundingMode &old) : nodeWrapper(old) {  IPRECONDITION(checkNodeType(node)); }

      // Not necessarily valid on creation
      roundingMode (const nonDetMarkerType &)
	: nodeWrapper(::CVC4::NodeManager::currentNM()->mkSkolem("nondet_roundingMode", 
								 ::CVC4::NodeManager::currentNM()->mkBitVectorType(5),
								 "created by symfpu")) {  IPRECONDITION(checkNodeType(node)); }

      proposition valid (void) const {
	::CVC4::NodeManager* nm = ::CVC4::NodeManager::currentNM();
	Node zero(nm->mkConst(::CVC4::BitVector(NUMRM, (long unsigned int)0)));

	// Is there a better encoding of this?
	return proposition(nm->mkNode(::CVC4::kind::AND, 
				      nm->mkNode(::CVC4::kind::EQUAL,
						 nm->mkNode(::CVC4::kind::BITVECTOR_AND,
							    this->node,
							    nm->mkNode(::CVC4::kind::BITVECTOR_SUB,
								       this->node,
								       nm->mkConst(::CVC4::BitVector(NUMRM, (long unsigned int)1)))),
						 zero),
				      nm->mkNode(::CVC4::kind::NOT,
						 nm->mkNode(::CVC4::kind::EQUAL,
							    this->node,
							    zero))));
      }

      proposition operator == (const roundingMode &op) const {
	return proposition(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::EQUAL, this->node, op.node));
      }


    };



    // Type function
    template <bool T> struct signedToLiteralType;

    template <> struct signedToLiteralType< true> {
      typedef int literalType;
    };
    template <> struct signedToLiteralType<false> {
      typedef  unsigned int literalType;
    };




    template <bool isSigned>
    class bitVector : public nodeWrapper {
    protected :
      typedef typename signedToLiteralType<isSigned>::literalType literalType;

      // TODO : make this private again
    public :

      bitVector (const Node n) : nodeWrapper(n) {  IPRECONDITION(checkNodeType(node)); }

      bool checkNodeType (const TNode n) {
	::CVC4::TypeNode tn = n.getType(false);
	return tn.isBitVector();
      }


      friend bitVector<!isSigned>;    // To allow conversion between the types
      friend ite<proposition, bitVector<isSigned> >;   // For ITE


    public :
      bitVector (const bitWidthType w, const unsigned v) : nodeWrapper(::CVC4::NodeManager::currentNM()->mkConst(::CVC4::BitVector(w, v))) { IPRECONDITION(checkNodeType(node)); }
      bitVector (const bitVector<isSigned> &old) : nodeWrapper(old) {  IPRECONDITION(checkNodeType(node)); }
      bitVector (const nonDetMarkerType &, const unsigned v)
	: nodeWrapper(::CVC4::NodeManager::currentNM()->mkSkolem("nondet_bitVector", 
								 ::CVC4::NodeManager::currentNM()->mkBitVectorType(v),
								 "created by symfpu")) { IPRECONDITION(checkNodeType(node)); }
      bitVector (const ::CVC4::BitVector &old) : nodeWrapper(::CVC4::NodeManager::currentNM()->mkConst(old)) { IPRECONDITION(checkNodeType(node)); }

      bitWidthType getWidth (void) const {
	return this->node.getType(false).getBitVectorSize();
      }


      /*** Constant creation and test ***/
      
      static bitVector<isSigned> one (const bitWidthType &w) { return bitVector<isSigned>(w,1); }
      static bitVector<isSigned> zero (const bitWidthType &w)  { return bitVector<isSigned>(w,0); }
      static bitVector<isSigned> allOnes (const bitWidthType &w)  { 
	return bitVector<isSigned>( ::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::BITVECTOR_NOT,
								 ::CVC4::NodeManager::currentNM()->mkConst(::CVC4::BitVector(w, (long unsigned int)0))) );
      }
      
      inline proposition isAllOnes() const {return (*this == bitVector<isSigned>::allOnes(this->getWidth()));}
      inline proposition isAllZeros() const {return (*this == bitVector<isSigned>::zero(this->getWidth()));}


      /*** Operators ***/
      inline bitVector<isSigned> operator << (unsigned s) const {
	IPRECONDITION(s <= this->getWidth());
	return bitVector<isSigned>(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::BITVECTOR_SHL, this->node, ::CVC4::NodeManager::currentNM()->mkConst(::CVC4::BitVector(this->getWidth(), s))));
      }

      inline bitVector<isSigned> operator << (const bitVector<isSigned> &op) const {
	return bitVector<isSigned>(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::BITVECTOR_SHL, this->node, op.node));
      }

      inline bitVector<isSigned> operator >> (uint64_t s) const {
	IPRECONDITION(s <= this->getWidth());
	return bitVector<isSigned>(::CVC4::NodeManager::currentNM()->mkNode((isSigned) ? ::CVC4::kind::BITVECTOR_ASHR : ::CVC4::kind::BITVECTOR_LSHR,
								  this->node,
									    ::CVC4::NodeManager::currentNM()->mkConst(::CVC4::BitVector(this->getWidth(), (long unsigned int)s))));
      }

      inline bitVector<isSigned> operator >> (const bitVector<isSigned> &op) const {
	return bitVector<isSigned>(::CVC4::NodeManager::currentNM()->mkNode((isSigned) ? ::CVC4::kind::BITVECTOR_ASHR : ::CVC4::kind::BITVECTOR_LSHR, this->node, op.node));
      }


      inline bitVector<isSigned> operator | (const bitVector<isSigned> &op) const {
	return bitVector<isSigned>(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::BITVECTOR_OR, this->node, op.node));
      }

      inline bitVector<isSigned> operator & (const bitVector<isSigned> &op) const {
	return bitVector<isSigned>(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::BITVECTOR_AND, this->node, op.node));
      }

      inline bitVector<isSigned> operator + (const bitVector<isSigned> &op) const {
	return bitVector<isSigned>(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::BITVECTOR_PLUS, this->node, op.node));
      }

      inline bitVector<isSigned> operator - (const bitVector<isSigned> &op) const {
	return bitVector<isSigned>(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::BITVECTOR_SUB, this->node, op.node));
      }

      inline bitVector<isSigned> operator * (const bitVector<isSigned> &op) const;

      inline bitVector<isSigned> operator - (void) const {
	return bitVector<isSigned>(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::BITVECTOR_NEG, this->node));
      }

      inline bitVector<isSigned> operator ~ (void) const {
	return bitVector<isSigned>(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::BITVECTOR_NOT, this->node));
      }

      inline bitVector<isSigned> increment () const {
	return bitVector<isSigned>(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::BITVECTOR_PLUS, this->node, ::CVC4::NodeManager::currentNM()->mkConst(::CVC4::BitVector(this->getWidth(), (long unsigned int)1))));
      }

      inline bitVector<isSigned> decrement () const {
	return bitVector<isSigned>(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::BITVECTOR_SUB, this->node, ::CVC4::NodeManager::currentNM()->mkConst(::CVC4::BitVector(this->getWidth(), (long unsigned int)1))));
      }

      inline bitVector<isSigned> signExtendRightShift (const bitVector<isSigned> &op) const {
	return bitVector<isSigned>(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::BITVECTOR_ASHR, this->node, op.node));
      }

      bitVector<isSigned> rightShiftStickyBit (const bitVector<isSigned> &op) const {
	bitVector<isSigned> stickyBit(ITE((op.orderEncode(this->getWidth()) & *this).isAllZeros(),
					  bitVector<isSigned>::zero(this->getWidth()),
					  bitVector<isSigned>::one(this->getWidth())));

	bitVector<isSigned> shifted(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::BITVECTOR_ASHR, this->node, op.node));
    
	return shifted | stickyBit;
      }


      /*** Modular opertaions ***/
      // No overflow checking so these are the same as other operations
      inline bitVector<isSigned> modularLeftShift (uint64_t s) const {
	IPRECONDITION(s <= this->getWidth());
	return *this << s;
      }

      inline bitVector<isSigned> modularIncrement () const {
	return this->increment();
      }

      inline bitVector<isSigned> modularAdd (const bitVector<isSigned> &op) const {
	return *this + op;
      }

      inline bitVector<isSigned> modularNegate () const {
	return -(*this);
      }




      /*** Comparisons ***/

      inline proposition operator == (const bitVector<isSigned> &op) const {
	return proposition(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::EQUAL, this->node, op.node));
      }

      inline proposition operator <= (const bitVector<isSigned> &op) const {
	return proposition(::CVC4::NodeManager::currentNM()->mkNode((isSigned) ? ::CVC4::kind::BITVECTOR_ULE : ::CVC4::kind::BITVECTOR_SLE, this->node, op.node));
      }

      inline proposition operator >= (const bitVector<isSigned> &op) const {
	return proposition(::CVC4::NodeManager::currentNM()->mkNode((isSigned) ? ::CVC4::kind::BITVECTOR_UGE : ::CVC4::kind::BITVECTOR_SGE, this->node, op.node));
      }

      inline proposition operator < (const bitVector<isSigned> &op) const {
	return proposition(::CVC4::NodeManager::currentNM()->mkNode((isSigned) ? ::CVC4::kind::BITVECTOR_ULT : ::CVC4::kind::BITVECTOR_SLT, this->node, op.node));
      }

      inline proposition operator > (const bitVector<isSigned> &op) const {
	return proposition(::CVC4::NodeManager::currentNM()->mkNode((isSigned) ? ::CVC4::kind::BITVECTOR_UGT : ::CVC4::kind::BITVECTOR_SGT, this->node, op.node));
      }

      /*** Type conversion ***/
      // CVC4 nodes make no distinction between signed and unsigned, thus ...
      bitVector<true> toSigned (void) const {
	return bitVector<true>(this->node);
      }
      bitVector<false> toUnsigned (void) const {
	return bitVector<false>(this->node);
      }



      /*** Bit hacks ***/

      inline bitVector<isSigned> extend (bitWidthType extension) const;

      inline bitVector<isSigned> contract (bitWidthType reduction) const {
	IPRECONDITION(this->getWidth() > reduction);

	::CVC4::NodeBuilder<> construct(::CVC4::kind::BITVECTOR_EXTRACT);
	construct << ::CVC4::NodeManager::currentNM()->mkConst< ::CVC4::BitVectorExtract>(::CVC4::BitVectorExtract((this->getWidth() - 1) - reduction, 0))
		  << this->node;
	
	return bitVector<isSigned>(construct);
      }

      inline bitVector<isSigned> resize (bitWidthType newSize) const {
	bitWidthType width = this->getWidth();

	if (newSize > width) {
	  return this->extend(newSize - width);
	} else if (newSize < width) {
	  return this->contract(width - newSize);
	} else {
	  return *this;
	}
      }

      inline bitVector<isSigned> matchWidth (const bitVector<isSigned> &op) const {
	IPRECONDITION(this->getWidth() <= op.getWidth());
	return this->extend(op.getWidth() - this->getWidth());
      }


      bitVector<isSigned> append(const bitVector<isSigned> &op) const {
	return bitVector<isSigned>(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::BITVECTOR_CONCAT, this->node, op.node));
      }

      // Inclusive of end points, thus if the same, extracts just one bit
      bitVector<isSigned> extract(bitWidthType upper, bitWidthType lower) const {
	IPRECONDITION(upper >= lower);

	::CVC4::NodeBuilder<> construct(::CVC4::kind::BITVECTOR_EXTRACT);
	construct << ::CVC4::NodeManager::currentNM()->mkConst< ::CVC4::BitVectorExtract>(::CVC4::BitVectorExtract(upper, lower))
		  << this->node;
	
	return bitVector<isSigned>(construct);
      }

      bitVector<isSigned> orderEncode (bitWidthType w) const {
	return (bitVector<isSigned>::one(w) << this->resize(w)).decrement();
      }



      /*** Expanding operations ***/

      inline bitVector<isSigned> expandingAdd (const bitVector<isSigned> &op) const {
	bitVector<isSigned> x((*this).extend(1));
	bitVector<isSigned> y(     op.extend(1));

	return x + y;
      }

      inline bitVector<isSigned> expandingSubtract (const bitVector<isSigned> &op) const {
	bitVector<isSigned> x((*this).extend(1));
	bitVector<isSigned> y(     op.extend(1));

	return x - y;
      }

      inline bitVector<isSigned> expandingMultiply (const bitVector<isSigned> &op) const {
	bitVector<isSigned> x((*this).extend(this->getWidth()));
	bitVector<isSigned> y(     op.extend(this->getWidth()));

	return x * y;
      }



    };

    /** CVC4's only multiply is unsigned
    inline bitVector<true> bitVector<true>::operator * (const bitVector<true> &op) const {
      return bitVector<true>(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::BITVECTOR_MULT, this->node, op.node));
    }
    */

    template <>
    inline bitVector<false> bitVector<false>::operator * (const bitVector<false> &op) const {
      return bitVector<false>(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::BITVECTOR_MULT, this->node, op.node));
    }

    template <>
    inline bitVector<true> bitVector<true>::extend(bitWidthType extension) const {
      ::CVC4::NodeBuilder<> construct(::CVC4::kind::BITVECTOR_SIGN_EXTEND);
      construct << ::CVC4::NodeManager::currentNM()->mkConst< ::CVC4::BitVectorSignExtend>(::CVC4::BitVectorSignExtend(extension))
		<< this->node;

      return bitVector<true>(construct);
    }

    template <>
    inline bitVector<false> bitVector<false>::extend(bitWidthType extension) const {
      ::CVC4::NodeBuilder<> construct(::CVC4::kind::BITVECTOR_ZERO_EXTEND);
      construct << ::CVC4::NodeManager::currentNM()->mkConst< ::CVC4::BitVectorZeroExtend>(::CVC4::BitVectorZeroExtend(extension))
		<< this->node;

      return bitVector<false>(construct);
    }


    class floatingPointTypeInfo {
    protected :
      //const ::CVC4::FloatingPointType type;
      const ::CVC4::TypeNode type;

      friend ite<proposition, floatingPointTypeInfo>;   // For ITE

    public :
      //    floatingPointTypeInfo(const ::CVC4::FloatingPointType t) : type(t) {}
      floatingPointTypeInfo(const ::CVC4::TypeNode t) : type(t) {
	IPRECONDITION(t.isFloatingPoint());
      }
      floatingPointTypeInfo(unsigned exp, unsigned sig) : type(::CVC4::NodeManager::currentNM()->mkFloatingPointType(exp,sig)) {}
      floatingPointTypeInfo(const floatingPointTypeInfo &old) : type(old.type) {}
      
      bitWidthType exponentWidth(void) const    { return this->type.getFloatingPointExponentSize(); }
      bitWidthType significandWidth(void) const { return this->type.getFloatingPointSignificandSize(); }
      
      bitWidthType packedWidth(void) const            { return this->exponentWidth() + this->significandWidth(); }
      bitWidthType packedExponentWidth(void) const    { return this->exponentWidth(); }
      bitWidthType packedSignificandWidth(void) const { return this->significandWidth() - 1; }
      
    };


    // Wrap up the types into one template parameter
    class traits {
    public :
      typedef bitWidthType bwt;
      typedef roundingMode rm;
      typedef floatingPointTypeInfo fpt;
      typedef proposition prop;
      typedef bitVector< true> sbv;
      typedef bitVector<false> ubv;

      static roundingMode RNE (void);
      static roundingMode RNA (void);
      static roundingMode RTP (void);
      static roundingMode RTN (void);
      static roundingMode RTZ (void);

      static void precondition(const prop &p);
      static void postcondition(const prop &p);
      static void invariant(const prop &p);
    };


  };


#define CVC4SYMITEDFN(T) template <>					\
    struct ite<cvc4_symbolic::proposition, T> {				\
    static const T iteOp (const cvc4_symbolic::proposition &cond,	\
			  const T &l,					\
			  const T &r) {					\
      return T(::CVC4::NodeManager::currentNM()->mkNode(::CVC4::kind::ITE, cond.getNode(), l.getNode(), r.getNode())); \
    }									\
  }

  // Can (unsurprisingly) only ITE things which contain Nodes  
  CVC4SYMITEDFN(cvc4_symbolic::traits::rm);
  CVC4SYMITEDFN(cvc4_symbolic::traits::prop);
  CVC4SYMITEDFN(cvc4_symbolic::traits::sbv);
  CVC4SYMITEDFN(cvc4_symbolic::traits::ubv);

};

#endif
