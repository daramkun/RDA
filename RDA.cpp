// C++ standard libraries
#include <stack>
#include <vector>
#include <string>

// LLVM components
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

#define DEBUG_TYPE "rda"

using namespace llvm;

namespace
{
	// Reaching Definition Analysis Pass
	struct RDA : public FunctionPass
	{
	public:
		static char ID;

	public:
		RDA () : FunctionPass ( ID ) { }
		~RDA () { }

	public:
		bool runOnFunction ( Function & f ) override
		{
			errs () << "Jin Jae-yeon's Reaching Definition Analysis\n";
			errs () << "Function name: ";
			errs ().write_escaped ( f.getName () ) << "\n";

			std::map<std::string, std::vector<unsigned>> allvar;
			std::map<llvm::Instruction*, unsigned> index;
			std::map<unsigned, std::string> names;
			unsigned indexCount = 0;

			// Collect all variable informations
			for ( Function::iterator bb = f.begin (); bb != f.end (); ++bb )
			{
				for ( BasicBlock::iterator i = ( *bb ).begin (); i != ( *bb ).end (); ++i )
				{
					if ( StoreInst * storeInst = static_cast<StoreInst*> ( &*i ) )
					{
						if ( storeInst->getPointerOperand ()->hasName () )
						{
							std::string name = storeInst->getPointerOperand ()->getName ();
							names.insert ( std::pair<unsigned, std::string> ( indexCount, name ) );
							if ( allvar.find ( name ) != allvar.end () )
							{
								std::vector<unsigned> temp;
								allvar.insert ( std::pair<std::string, std::vector<unsigned>> ( name, std::vector<unsigned> () ) );
							}
							index.insert ( std::pair<llvm::Instruction*, unsigned> ( storeInst, indexCount ) );
							allvar [ name ].push_back ( indexCount );
							++indexCount;
						}
					}
				}
			}
			errs () << "Collected all variable informations.\n";
			for ( auto vi = allvar.begin (); vi != allvar.end (); ++vi )
			{
				auto v = *vi;
				errs () << "VAR [" << v.first << "]: ";
				auto is = v.second;
				for ( auto i = is.begin (); i != is.end (); ++i )
					errs () << *i << " ";
				errs () << "\n";
			}
			errs () << "-------------------\n";

			// Collect GEN/KILL for Reaching Definition Analysis
			errs () << "~~~ GEN/KILL ~~~\n";

			std::map<llvm::BasicBlock*, std::vector<unsigned>> gens;
			std::map<llvm::BasicBlock*, std::vector<unsigned>> kills;
			std::vector<llvm::BasicBlock*> basicblocks;

			// Looping Basic blocks
			for ( Function::iterator bb = f.begin (); bb != f.end (); ++bb )
			{
				BasicBlock & b = *bb;
				std::vector<unsigned> gen;
				std::vector<unsigned> kill;
				
				// Looping instructions
				for ( BasicBlock::iterator i = b.begin (); i != b.end (); ++i )
				{
					if ( StoreInst * storeInst = static_cast<StoreInst*> ( &*i ) )
					{
						if ( allvar.find ( storeInst->getPointerOperand ()->getName () ) == allvar.end () )
							continue;
						
						unsigned id = index [ storeInst ];
						// gen
						if ( std::find ( gen.begin (), gen.end (), id ) == gen.end () )
							gen.push_back ( id );
						std::sort ( gen.begin (), gen.end () );
						// kill
						std::vector<unsigned> others = allvar [ storeInst->getPointerOperand ()->getName () ];
						for ( auto o = others.begin (); o != others.end (); ++o )
						{
							if ( std::find ( gen.begin (), gen.end (), *o ) != gen.end () ) continue;
							if ( std::find ( kill.begin (), kill.end (), *o ) == kill.end () )
								kill.push_back ( *o );
						}
					}
				}

				// Delete from KILL if contained GEN
				for ( auto k = kill.begin (); k != kill.end (); ++k )
					for ( auto g = gen.begin (); g != gen.end (); ++g )
						if ( *k == *g )
							kill.erase ( k );
				std::sort ( kill.begin (), kill.end () );

				errs () << "GEN: ";
				for ( auto g = gen.begin (); g != gen.end (); ++g )
					errs () << *g << " ";
				errs () << "\n";
				errs () << "KILL: ";
				for ( auto k = kill.begin (); k != kill.end (); ++k )
					errs () << *k << " ";
				errs () << "\n";
				errs () << "============================================\n";
				
				gens.insert ( std::pair<llvm::BasicBlock*, std::vector<unsigned>> ( &b, gen ) );
				kills.insert ( std::pair<llvm::BasicBlock*, std::vector<unsigned>> ( &b, kill ) );

				basicblocks.push_back ( &b );
			}

			// Collect IN/OUT for Reaching Definition Analysis
			errs () << "~~~ IN/OUT ~~~\n";

			std::map<llvm::BasicBlock*, std::vector<unsigned>> ins;
			std::map<llvm::BasicBlock*, std::vector<unsigned>> outs;

			// Tracing BasicBlocks
			while ( basicblocks.size () > 0 )
			{
				for ( auto bb = basicblocks.begin (); bb != basicblocks.end (); )
				{
					BasicBlock * temp = *bb;

					std::vector<unsigned> in;
					std::vector<unsigned> out;

					std::vector<unsigned> myGen = gens [ temp ];
					std::vector<unsigned> myKill = kills [ temp ];

					// Is this Basicblock Entrypoint?
					if ( pred_begin ( temp ) != pred_end ( temp ) )
					{
						// Predecessor's is ready?
						bool predecessorNotProceed = false;
						for ( pred_iterator pi = pred_begin ( temp ); pi != pred_end ( temp ); ++pi )
							if ( outs.find ( *pi ) == outs.end () )
								predecessorNotProceed = true;

						if ( predecessorNotProceed )
						{
							++bb;
							continue;
						}
					}

					// Collect IN from predecessors
					for ( pred_iterator pi = pred_begin ( temp ); pi != pred_end ( temp ); ++pi )
					{
						BasicBlock * predecessor = *pi;
						std::vector<unsigned> pout = outs [ predecessor ];
						for ( auto poi = pout.begin (); poi != pout.end (); ++poi )
						{
							if ( std::find ( in.begin (), in.end (), *poi ) == in.end () )
								in.push_back ( *poi );
						}
					}
					std::sort ( in.begin (), in.end () );

					// Collect OUT
					std::vector<unsigned> intemp ( in );
					for ( auto g = myGen.begin (); g != myGen.end (); ++g )
					{
						std::string myName = names [ *g ];
						std::vector<unsigned> friends = allvar [ myName ];
						for ( auto fr = friends.begin (); fr != friends.end (); ++fr )
						{
							auto found = std::find ( intemp.begin (), intemp.end (), *fr );
							if ( found != intemp.end () )
								intemp.erase ( found );
						}
						intemp.push_back ( *g );
					}
					for ( auto t = intemp.begin (); t != intemp.end (); ++t )
						out.push_back ( *t );
					std::sort ( out.begin (), out.end () );

					ins.insert ( std::pair<llvm::BasicBlock*, std::vector<unsigned>> ( temp, in ) );
					outs.insert ( std::pair<llvm::BasicBlock*, std::vector<unsigned>> ( temp, out ) );

					basicblocks.erase ( bb );
				}
			}

			for ( auto bb = f.begin (); bb != f.end (); ++bb )
			{
				std::vector<unsigned> in = ins [ &*bb ];
				std::vector<unsigned> out = outs [ &*bb ];

				errs () << "IN: ";
				for ( auto i = in.begin (); i != in.end (); ++i )
					errs () << *i << " ";
				errs () << "\n";
				errs () << "OUT: ";
				for ( auto o = out.begin (); o != out.end (); ++o )
					errs () << *o << " ";
				errs () << "\n";
				errs () << "=========================================\n";
			}
			
			// COMPLETE
			return true;
		}
	};
}

char RDA::ID = 0;
static RegisterPass<RDA> X ( "rda", "Reaching Definition Analysis Pass" );

