import YM.RG08.Isles.Shores

/-!
# Port resolution and cofinal dominated convergence for sums whose positions can be viewed
on bigger and bigger tori. Prices in this chapter for pure removal of the regulator at one
step do not commute with the N (number of levels) reports; use separately only for cofinal
identity comparisons.
-/
noncomputable section
namespace YM.RG08.Isles
open Forms Pert.Bulk Packets Laurent Finset Function Lattice Filter
open scoped Topology BigOperators ENNReal Classical
set_option autoImplicit false
variable {I J Y:Type}{Z:ℕ→Type}

structure Route (Y:Type)(Z:ℕ→Type) where
 out:(i:ℕ)→Z i→Y
 visit:(i:ℕ)→Y→Z i
 same (i)(z:Z i):visit i (out i z)=z
 growing (y:Y):∀ᶠ i:ℕ in atTop,out i (visit i y)=y

def Route.prod {Y':Type}{Z':ℕ→ Type}(a:Route Y Z)(b:Route Y' Z'):Route (Y×Y') (fun i=>Z i×Z' i) where
 out i x:=(a.out i x.1,b.out i x.2)
 visit i x:=(a.visit i x.1,b.visit i x.2)
 same i x:=by simp [a.same,b.same]
 growing x:=by filter_upwards [a.growing x.1,b.growing x.2] with i hi hj;simp [hi,hj]

def Route.cards (a:Route Y Z)(n:ℕ):Route (Tape n Y) (fun i=> Tape n (Z i)) where
 out i x:=a.out i ∘ x
 visit i x:=a.visit i ∘ x
 same i x:=by ext j;simp [a.same]
 growing x:=by filter_upwards [Filter.eventually_all.mpr (fun j:Fin n=>a.growing (x j))] with i hi;ext j;simp [hi]

lemma DCT (R:Route Y Z)[∀ i,Fintype (Z i)](f:(i:ℕ)→ Z i→ℝ)(F B:Y→ℝ)(h:∀ y, Tendsto (fun i=> f i (R.visit i y)) atTop (𝓝 (F y))) (hs:Summable B)(hn:∀ y,0≤B y)
    (hp:∀ᶠ i:ℕ in atTop,∀ x:Z i,‖f i x‖≤B (R.out i x)):
    Tendsto (fun i=>∑' x,f i x) atTop (𝓝 (∑' x,F x)):=by
 let U(i)(x:Y):= if R.out i (R.visit i x)=x then f i (R.visit i x) else 0
 have ht(x:Y):Tendsto (fun i=> U i x) atTop (𝓝 (F x)):= (h x).congr' ((R.growing x).mono fun i hi=> (if_pos hi).symm)
 have he(i:ℕ):(∑' x:Y,U i x)=∑' x,f i x:=by
   have hh : Injective (R.out i):=LeftInverse.injective (g:=R.visit i) (R.same i)
   have ho(x:Y):U i x=∑ y: Z i,if x=R.out i y then f i y else 0:=by
     unfold U;split_ifs with hx
     · rw [←hx];simp_rw [hh.eq_iff,Finset.sum_ite_eq,if_pos (mem_univ _), R.same]
     · symm;apply sum_eq_zero;intro j _; apply if_neg; rintro rfl;exact hx (by rw [R.same])
   simp_rw [ho,Summable.tsum_finsetSum (fun y _=>summable_of_ne_finset_zero (s:={R.out i y}) (fun x hx=>if_neg (by simpa using hx))),tsum_fintype] -- tsum_fintype interferes tsum_ite
   simp [tsum_ite_eq]
 have hu : ∀ᶠ i in atTop,∀ x:Y, ‖U i x‖≤B x:=hp.mono (fun i hi x=>by
    unfold U;split
    · rename_i H
      calc
        _ ≤ B (R.out i (R.visit i x)) := hi (R.visit i x)
        _ = B x := congrArg B H
    · rw [norm_zero];exact hn x)
 exact (tendsto_tsum_of_dominated_convergence hs ht hu).congr' (Eventually.of_forall he)

variable (I)
def colony (i:ℕ):=Cove (chain i) I
instance colony_finite [Fintype I] (i:ℕ): Fintype (colony I i):=inferInstanceAs (Fintype (Cove (chain i) I))
def carpetRoad : Route (Market I) (colony I) where
 out _:= reach
 visit i:= port (chain i)
 same _:= reaches
 growing:=contacts

variable {I}{n:ℕ}
abbrev ViewDeck (n:ℕ)(I:Type):=(i:ℕ)→Flake n (colony I i)

def Eyes (f:ViewDeck n I)(F:Flake n (Market I)):=∀ x, Tendsto (fun i=>f i ((carpetRoad I).visit i ∘ x)) atTop (𝓝 (F x))

/-- A possibly winding-corrected periodic tensor and cover candidate coefficients; first charge
position diameter independent of torus size. At arity zero `Eyes` won't generally be
required. -/
structure Study (σ p:ℝ)(f:ViewDeck n I)(F:Flake n (Market I)):Prop where
 rate : 0<σ
 cost : 0≤p
 palm : Held (carpet I) σ p F
 calm i : Held (shore (chain i) I) σ p (f i)
 light (_:0<n): Eyes f F

variable {F G:Flake n (Market I)}{f g:ViewDeck n I}{σ τ p q:ℝ}
lemma Study.mono (h:Study σ p f F)(hτ:0<τ)(hs:τ≤σ)(hp:p≤q):Study τ q f F:=⟨hτ,h.cost.trans hp,h.palm.mono hs hp (fun _=>le_rfl),fun i=>(h.calm i).mono hs hp (fun _=>le_rfl),h.light⟩
lemma Study.add (h:Study σ p f F)(H:Study σ q g G):Study σ (p+q) (f+g) (F+G):=⟨h.rate,by have he:=h.cost;have hx:=H.cost;positivity,h.palm.add H.palm h.cost H.cost,fun i=>(h.calm i).add (H.calm i) h.cost H.cost,fun hn x=>(h.light hn x).add (H.light hn x)⟩
lemma Study.smul (h:Study σ p f F)(t:ℝ): Study σ (|t| * p) (t • f) (t • F):=⟨h.rate,by have he:=h.cost;positivity,h.palm.smul t,fun i=>(h.calm i).smul t,fun hn x=>(h.light hn x).const_mul t⟩
lemma Study.zero (I:Type)(n:ℕ)(h:0<σ)(hp:0≤p):Study σ p (0:ViewDeck n I) 0:=⟨h,hp,zero_held,fun _=>zero_held,fun _ _=> tendsto_const_nhds⟩
lemma Study.blank (h:0<σ){f:ViewDeck 0 I}{F}:Study σ 0 f F:=⟨h,le_refl _,ensign.mpr fun i=>Fin.elim0 i,fun _=>ensign.mpr fun i=>Fin.elim0 i,fun hh=>False.elim (Nat.lt_irrefl 0 hh)⟩
lemma Study.sum (S:Finset J)(hs:0<σ)(p:J→ℝ)(f:J→ViewDeck n I)(F:J→Flake n (Market I))(h:∀ i∈S,Study σ (p i) (f i) (F i)):Study σ (S.sum p) (S.sum f) (S.sum F):=by induction S using Finset.induction_on with
 | empty=>simp only [sum_empty];exact zero I n hs le_rfl
 | insert _ _ he ih=>rw [sum_insert he,sum_insert he,sum_insert he];exact (h _ (mem_insert_self ..)).add (ih fun i hi=>h i (mem_insert_of_mem hi))
lemma Study.bleach (h:Study σ p f F):Study σ p (fun i=>bleach (f i)) (bleach F):=by
 refine ⟨h.rate,h.cost,h.palm.bleach h.cost,fun i=>(h.calm i).bleach h.cost,fun hn x=>?_⟩
 simp only [Forms.bleach,Pi.smul_apply,smul_eq_mul,Finset.sum_apply,woven]
 refine Tendsto.const_mul _ (tendsto_finsetSum _ fun e _=> ?_)
 exact h.light hn (x ∘ e)
end YM.RG08.Isles
