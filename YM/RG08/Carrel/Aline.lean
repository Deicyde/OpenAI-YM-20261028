import YM.RG08.Carrel.Kiss

/-! # Fake-period evaluation and linear reconstruction. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Carrel
open Camera Cloud Room Glyph
open Lattice Laurent Forms Pert.Bulk Isles Packets Filter Finset Function RG
open Wilson Exterior Push.Uniform Precision Work.F03 Extra.Iteration MvPolynomial
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{n:ℕ}{P:Side}

def attic (n:ℕ):Side:=⟨2*n+1,by positivity⟩
lemma right_attic {x:Cover}(r:ℕ)(h:size x≤r):lift (wrap (attic r) x)= x:=by
 apply lift_eq_iff.mpr;refine ⟨rfl,fun i=>?_⟩;have hh: (x i).natAbs≤r:=(show (x i).natAbs≤size x from Finset.single_le_sum (fun i (_:i∈(univ:Finset Axis))=> Nat.zero_le (x i).natAbs) (mem_univ i)).trans h
 change -((2*r+1:ℕ):ℤ)<2*x i∧2*x i≤((2*r+1:ℕ):ℤ);omega
lemma attic_left (r:ℕ)(x:Site (attic r)):size (lift x)≤4*r:=by
 have ht(i:Axis):(lift x i).natAbs≤r:=by
    obtain ⟨h,H⟩:=lift_centers x i; change -((2*r+1:ℕ):ℤ)<2*lift x i at h; change 2*lift x i≤((2*r+1:ℕ):ℤ) at H;omega
 apply (Finset.sum_le_sum (s:=univ) (fun i _=>ht i)).trans_eq; simp [Axis]

lemma regions (s:Slot){x:Cover}(h:x∈s.stencil):size x≤s.length:=by
 rw [Slot.stencil,mem_union] at h
 simp only [List.mem_toFinset] at h
 cases h with
 | inl h=>have he:=Extra.Iteration.along_size 0 _ _ h; unfold Slot.length;simp only [sub_zero] at he; omega
 | inr h=>have he:=Extra.Iteration.along_size _ _ _ h; have hf:= Extra.Iteration.offset_size s
          simp only [Lattice.square, List.length_cons,List.length_nil] at he
          apply le_trans (b:=size (x-s.offset)+size s.offset)
          · exact (by simpa only [sub_add_cancel] using size_add (x-s.offset) s.offset)
          unfold Slot.length; omega

def depositAt (r:ℕ)(o:Site P)(i:Bedge G (attic r)): Bedge G P:=(wrap P (lift i.1)+o, i.2)
def molds (r:ℕ)(o:Site P):Strip (Bedge G (attic r)) (Bedge G P):=fun i x=>x (depositAt r o i)
lemma molds_pace (r:ℕ)(o:Site P)(i:Bedge G (attic r)):Pace (molds r o i):=contDiffAt_apply ..
lemma mold_slot (r:ℕ)(o:Site P)(x:Cellar (Bedge G P))(s:Slot)(hs:s.length≤r):
 s.atSite (offers G (roll (molds r o) x)) (0:Site (attic r)) = s.atSite (offers G x) o:=by
 apply s.covered;intro e he _
 unfold expandAt offers;congr 1 -- maybe group proof
 ext i
 rw [inserts,inserts]; unfold molds roll depositAt; simp [right_attic r ((regions s he).trans hs)]

lemma attic_atom (r:ℕ)(a:Atom G n)(ha:a.length≤r)(o:Site P):showAtom a o = showAtom a (0:Site (attic r)) ∘ roll (molds r o):=by
 funext x;unfold showAtom Atom.unmasked; dsimp only [comp_apply];rw [funext fun i=>mold_slot r o x (a.leg i) ((Finset.single_le_sum (s:=univ) (fun j _=> Nat.zero_le (a.leg j).length) (mem_univ i)).trans ha)]
lemma molds_shoot (r:ℕ)(o:Site P)(i:Bedge G (attic r)):rescaleFields (molds r o) i=rod (depositAt r o i):=by unfold rescaleFields molds;rw [Camera.lamp];ext e :1;change tap e _=tap e _;rw [look,hopper]

lemma attic_deck (a:Atom G n)(o:Site P)(k:ℕ): print (I:=Bedge G P) k (showAtom a o)= MvPolynomial.rename (depositAt a.length o) (print k (showAtom a (0:Site (attic a.length)))):=by
 let f:=showAtom a (0:Site (attic a.length))
 have hf:Pace f:=by obtain ⟨C,hc,h⟩:=per_atom G n 0 (η:=1) zero_lt_one;exact (h a _ _).analytic
 rw [attic_atom a.length a le_rfl,←flute,flask_comp (molds_pace _ o) rfl hf]
 rw [funext (molds_shoot (G:=G) a.length o)]
 change tap k (spool (lug _) _)=_
 let D:=depositAt (G:=G) a.length o
 have he(p:Inn (Bedge G (attic a.length))):lug (fun i=>rod (D i)) p=liftInn (MvPolynomial.rename D p):=by
    induction p using MvPolynomial.induction_on with
    | C b=>unfold lug;rw [aeval_C,rename_C,PowerSeries.algebraMap_apply];rfl
    | add _ _ h H=>simp only [map_add,h,H]
    | mul_X p j h=>rw [_root_.map_mul,_root_.map_mul,_root_.map_mul,h,rename_X,lug,aeval_X]
 change tap k (spool (lug fun i=>rod (D i)) _)=_
 rw [Room.ships];simp_rw [he,flute];rw [Finset.sum_eq_single k (fun i hi hii=>by rw [tap,PowerSeries.coeff_C, if_neg (by simp only [mem_range] at hi;omega)]) (by simp)];simp [tap];rfl

/-- path terms now entirely cover: $N$ external fields appear exactly at g^N in an analytic
completion germ. Keep the expansion as occurrences at virtual torus in proof only (no actual
N/paging). H.Compressions assign one per rooted input template. -/
def stored (a:Atom G n)(N:ℕ) (x:Slide (Rayk G 1) N):ℝ:=∑ i:Tape N (Bedge G (attic a.length)),if x= (reach ∘ i) then Camera.deck N (showAtom a (0:Site (attic a.length))) i else 0

lemma stored_view (a:Atom G n)(o:Site P)(N:ℕ)(v:Vert P (Rayk G 1)):
 eval v (tap N (flask (showAtom a o))) = ∑' x,stored a N x*per_use x v o:=by
 rw [flute,attic_deck,←deck_parley,parley,map_sum] -- rename ν
 simp_rw [eval_sum] -- name
 unfold stored;simp_rw [Finset.sum_mul,ite_mul,zero_mul]
 rw [Summable.tsum_finsetSum]
 · simp_rw [tsum_ite_eq,_root_.map_smul,MvPolynomial.smul_eq_C_mul,eval_mul,eval_C,word,map_prod,rename_X,eval_X];rfl
 intro j _;apply summable_of_ne_finset_zero (s:={reach ∘ j});intro x hx; simp only [mem_singleton] at hx;exact if_neg hx
end YM.RG08.Carrel
