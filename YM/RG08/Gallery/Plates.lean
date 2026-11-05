import YM.RG08.Fold.Fixtures

/-!
# Raw-law transmissions on sparse test values (formal series)
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Gallery
open Forms Glyph Room Camera Finset Lattice Laurent Pert.Bulk Function MvPolynomial Filter
open scoped Topology BigOperators ContDiff PowerSeries Classical
variable {I J K:Type}{n:ℕ}

abbrev Dig := PowerSeries ℝ
structure Tray (I:Type) where
 base: Finset I
 get:I→Dig
 shut: ∀ x∉base,get x=0

def fret (x:I→Dig)(t:Tape n I):Dig:=∏ i,x (t i)

def desks (S:Finset I)(n:ℕ):Finset (Tape n I):=Fintype.piFinset (fun _=>S)
lemma desks_out {x:Tape n I}{a:I→Dig}{S:Finset I}(h:∀ i∉S,a i=0)(hx:x∉desks S n):fret a x=0:=by
 have ht:¬∀ i:Fin n,x i∈S := by simpa [desks] using hx
 obtain ⟨i,hi⟩:=Classical.not_forall.mp ht
 exact Finset.prod_eq_zero (mem_univ i) (h _ hi)
def volume (F:Flake n I)(a:Tray I):Dig:= ∑ x∈desks a.base n,F x • fret a.get x
lemma volume_s (F:Flake n I)(a:Tray I)(S:Finset I)(ht:a.base⊆S):volume F a=∑ x∈desks S n,F x • fret a.get x:= Finset.sum_subset (fun i hi=> by simp only [desks,Fintype.mem_piFinset] at *;exact fun j=>ht (hi j)) fun b _ h=>by rw [desks_out a.shut h,smul_zero]

variable [Fintype I]
lemma melody (F:Flake n I)(W:I→Dig):MvPolynomial.aeval W (parley F)=∑ t:Tape n I,F t • fret W t:=by simp only [parley,map_sum,_root_.map_smul,word,map_prod,aeval_X];rfl
lemma vat (F:Flake n I)(u:Tray I):volume F u=MvPolynomial.aeval u.get (parley F):=by rw [melody,volume_s _ _ univ (subset_univ _)];simp [desks]

/-- Evaluate FPS in SPS via cable spools, no continuity needed. -/
def breath (u:I→Dig):Port I→ₐ[ℝ] Dig:= tie (MvPolynomial.aeval u)
omit [Fintype I] in
lemma pulses (u:I→Dig)(f:Port I)(e:ℕ):tap e (breath u f)=∑ i∈Finset.range (e+1),tap (e-i) (MvPolynomial.aeval u (tap i f)):= Room.ships (MvPolynomial.aeval u) f _
omit [Fintype I] in
lemma bases (u:I→Dig)(f:Inn I): breath u (liftInn f)=MvPolynomial.aeval u f:=Room.tack_c ..
omit [Fintype I] in
lemma bases_x (u:I→Dig)(i:I):breath u (rod i)=u i:=by rw [bases];exact aeval_X ..
omit [Fintype I] in
lemma bases_g (u:I→Dig):breath u PowerSeries.X=PowerSeries.X:=Room.tack_x ..
omit [Fintype I] in
lemma fugue (u:I→Dig)(b:J→Port I)(f:Port J): breath u (belt b f)=breath (fun j=>breath u (b j)) f:=by
 ext i :1
 let q:=tube (PowerSeries.C:Inn J→Cab (Inn J)) f i
 have he(k)(hk:k ≤ i):tap k f=tap k q:=by unfold q; rw [←tubes _ _ _ _ hk,direct]
 change tap i _=tap i _
 have hs{I : Type}(u:I→Dig)(i:ℕ){f g:Port I}(he:∀ k ≤ i,tap k f=tap k g):tap i (breath u f)=tap i (breath u g):= rewire (MvPolynomial.aeval u) _ he
 rw [hs (g:=belt b q) _ i (fun k hk=>steady_belt b _ _ _ (fun j hj=>he j (hj.trans hk))),hs _ _ he]; apply congrArg
 have hh(a:Inn J):breath u (belt b (liftInn a))=breath (fun j=>breath u (b j)) (liftInn a):=by
    induction a using MvPolynomial.induction_on with
    | C x=>rw [belt_c,lug,aeval_C]; simp only [AlgHom.commutes,bases,aeval_C]
    | add _ _ hi hj=> simp only [map_add,hi,hj]
    | mul_X a j ha=>rw [_root_.map_mul,_root_.map_mul,_root_.map_mul,_root_.map_mul,ha];change _ * breath u (belt b (rod j))=_ * breath _ (rod j);rw [belt_x,bases_x]
 unfold q tube;simp only [map_sum,_root_.map_mul,_root_.map_pow,belt_g,bases_g,show (PowerSeries.C:Inn J→+*Cab (Inn J))=liftInn from rfl,hh]

-- full rank symbol at every e, including e=0 bare quadratic, use both zero and positive
-- e. C2.1 stock uses cover/finite with support caps identity.
abbrev Script (I:Type) := Steam.Grain I

def dubbed (V:Script I)(e:ℕ)(a:Tray I):Dig:=∑ k∈range (e+3),Gallery.volume (V e k) a

def announced (V:Script I)(a:Tray I):Dig:=PowerSeries.mk (fun e=> ∑ i∈range (e+1),tap (e-i) (dubbed V i a))

-- paths output uses subtraction before pointwise cofinal, extensive scalars cancel because
-- same V on both readings. Keep explicitly.
lemma cry (V:Script I)(a:Tray I):breath a.get (stock V)=announced V a:=by
 ext e :1
 rw [show PowerSeries.coeff _ (breath a.get _)=_ from pulses _ _ e, announced,PowerSeries.coeff_mk]; apply Finset.sum_congr rfl;intro i hi
 simp only [tap,Glyph.stock,PowerSeries.coeff_mk,Glyph.showV,map_sum,dubbed,vat]
end YM.RG08.Gallery
