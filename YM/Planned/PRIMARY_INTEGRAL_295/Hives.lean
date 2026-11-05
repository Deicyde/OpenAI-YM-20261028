import YM.Planned.PRIMARY_INTEGRAL_295.Chrysalis
/-!
# Color rotation & explicit closure of selected fibers

For actual compressed W and anchored.Odd. Keeps unfilled identities. All these
matrix propagations on fixed assigned rows. No assertion the required K.D transforms
before cut if V mismatched. Laws assume complete color roster on every test; can't
reorient C half alone. Sky presentation later. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Hives
open Function Filter Set Metric MeasureTheory ProbabilityTheory Matrix Finset
open Lattice RG Wilson Pressure Labels Source
open Precision Exterior Tree Carrier Bloch Progress.StationaryScenes Bazaars Launch Shapes
open Villa Floor Glints Fizz Fizz.Gush Little Density Little.Core Push.Uniform  
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace -- careful DecEq α
variable {G:Gauge}
variable {α β X W : Type*}

-- diagonal blocks named α. vectors true finite log y.
structure Hive (G:Gauge) (X α:Type*) where
   entry : X ↪ α × G.ColorIndex
   pick : X → G.ColorIndex → X
   hatch (i:X)(j:G.ColorIndex): entry (pick i j) = ((entry i).1,j)

variable (H:Hive G X α)
namespace Hive
variable (z:α→G.El)
def room (x:X) := (H.entry x).1
def ink (x:X) := (H.entry x).2
@[simp] lemma room_pick (x:X) (i:G.ColorIndex): H.room (H.pick x i)= H.room x:= by unfold room; rw [H.hatch]
@[simp] lemma ink_pick (x:X) (i:G.ColorIndex): H.ink (H.pick x i)= i:= congr_arg Prod.snd (H.hatch x i)
@[simp] lemma pick_self (x:X): H.pick x (H.ink x)=x:= H.entry.injective (H.hatch x (H.ink x))
@[simp] lemma pick_again (x:X) (i j:G.ColorIndex): H.pick (H.pick x i) j= H.pick x j:=
   H.entry.injective (by rw [H.hatch,H.hatch,H.hatch])

lemma pickable {i j:X}(hp:H.room i=H.room j)(k:G.ColorIndex): H.pick i k=H.pick j k:=
    H.entry.injective (by rw [H.hatch,H.hatch]; exact Prod.ext hp rfl)

def bunch (f:X→ℝ)(x:X):G.Color:= WithLp.toLp 2 (f ∘ H.pick x)
def burn : (X→ℝ)→ₗ[ℝ] (X→ℝ) where
   toFun f x:= (G.adjoint (z (H.room x)) (H.bunch f x)) (H.ink x)
   map_add' f g:=by ext x; rw [show H.bunch (f+g) x=H.bunch f x+H.bunch g x from rfl,map_add]; rfl
   map_smul' q f:=by ext x; rw [show H.bunch (q • f) x=q • H.bunch f x from rfl,map_smul]; rfl
lemma bump (x y:X)(hp:H.room x=H.room y)(f:X→ℝ):H.bunch f x=H.bunch f y:=by unfold bunch; rw [funext (H.pickable hp)]
lemma bless (f:X→ℝ)(i:X): H.bunch (H.burn z f) i = G.adjoint (z (H.room i)) (H.bunch f i):=by
   apply PiLp.ext; intro j;
   change G.adjoint (z (H.room (H.pick i j))) (H.bunch f (H.pick i j)) (H.ink (H.pick i j))=G.adjoint (z (H.room i)) (H.bunch f i) j
   have hx := H.bump (H.pick i j) i (H.room_pick ..) f
   rw [hx,H.ink_pick i j,H.room_pick i j]
lemma uniform (f:X→ℝ)(i:X): H.bunch f i (H.ink i)=f i:=by change f _=_; rw [H.pick_self]
lemma cars (f:X→ℝ)(v:α→G.El): H.burn z (H.burn v f)=H.burn (z*v) f:=by
   ext i; change G.adjoint _ _ _= G.adjoint _ _ _; rw [bless,Pi.mul_apply,G.adjoint_mul]
@[simp] lemma check (f:X→ℝ): H.burn 1 f=f:=by ext i; change G.adjoint 1 _ _ = _; rw [G.adjoint_one]; exact H.uniform f i

def swab : (X→ℝ) ≃ₗ[ℝ] (X→ℝ) := LinearEquiv.ofLinear (H.burn z) (H.burn z⁻¹)
    (LinearMap.ext fun f=>show H.burn z (H.burn z⁻¹ f)=f from by rw [cars,mul_inv_cancel,H.check])
    (LinearMap.ext fun f=> show H.burn z⁻¹ (H.burn z f)=f from by rw [cars,inv_mul_cancel,H.check])

variable [Fintype X] [DecidableEq X]
def paint : Matrix X X ℝ:= Matrix.of fun i j=> H.burn z (Pi.single j 1) i
lemma pigment (f:X→ℝ) : (H.paint z).mulVec f = H.burn z f:=by
    have hx : (∑ i:X,f i • (Pi.single i 1 : X→ℝ))=f:=by ext i; simp [Finset.sum_apply,Pi.single_apply]
    ext i; nth_rw 2 [← hx]; rw [map_sum,Finset.sum_apply]; apply Finset.sum_congr rfl; intro j _; rw [map_smul]; change H.paint z i j * f j = f j * H.paint z i j; exact mul_comm _ _
-- entry θ transpose using inner pair.Avoid multiplying norm. exact axis inner.
omit [Fintype X] in
lemma tone (i j:X) (hp:H.room i ≠ H.room j) :(H.paint z) i j=0:=by
    have he:H.bunch (Pi.single j 1) i=0:=by
       ext x; change (Pi.single j 1 : X → ℝ) _=0
       apply Pi.single_eq_of_ne; intro hj; apply hp; exact (H.room_pick i x).symm.trans (congr_arg H.room hj)
    change G.adjoint _ _ _=0; rw [he,map_zero]; rfl
omit [Fintype X] in
lemma pestle (i j:X) (hp:H.room i=H.room j):(H.paint z) i j=
     G.adjoint (z (H.room i)) (EuclideanSpace.single (H.ink j) (1:ℝ)) (H.ink i):=by
    have he:H.bunch (Pi.single j 1) i=EuclideanSpace.single (H.ink j) (1:ℝ):=by
       ext x; by_cases hh:x=H.ink j
       · rw [hh]; change (Pi.single j 1 : X→ℝ) _=(Pi.single (H.ink j) 1:G.ColorIndex→ℝ) _; rw [H.pickable hp,H.pick_self]; simp
       change (Pi.single j 1 : X→ℝ) _=(Pi.single (H.ink j) 1:G.ColorIndex→ℝ) _; rw [Pi.single_eq_of_ne hh,Pi.single_eq_of_ne]
       intro hk; exact hh ((H.ink_pick i x).symm.trans (congr_arg H.ink hk))
    change G.adjoint _ _ _=_; rw [he]
omit [Fintype X] in
lemma reflection : (H.paint z).transpose=H.paint z⁻¹:=by
    classical
    have he (u:G.El)(x y:G.Color):inner ℝ (G.adjoint u x) (G.adjoint u y)=inner ℝ x y:=by
        let L : G.Color →ₗᵢ[ℝ] G.Color:={G.adjoint u with norm_map':=G.norm_adjoint u}; exact L.inner_map_map x y
    ext i j; change H.paint z j i=_; by_cases hx:H.room j=H.room i
    · rw [H.pestle z j i hx,H.pestle _ i j hx.symm,hx]
      let f(v):=EuclideanSpace.single (H.ink v) (1:ℝ); let u:= z (H.room i)
      have hp:= he u (f i) (G.adjoint u⁻¹ (f j)); rw [← G.adjoint_mul,mul_inv_cancel,G.adjoint_one] at hp
      simpa only [Pi.inv_apply,u,f,EuclideanSpace.inner_single_left,EuclideanSpace.inner_single_right, RCLike.star_def,conj_trivial,mul_one,one_mul] using hp
    rw [H.tone z j i hx,H.tone _ i j (Ne.symm hx)]
lemma cups : H.paint z*H.paint z⁻¹=1:=by
    let U:=H.paint z*H.paint z⁻¹
    have he (i:X): U *ᵥ Pi.single i 1 = Pi.single i 1:=by unfold U; rw [←mulVec_mulVec,H.pigment,H.pigment,H.cars,mul_inv_cancel,H.check]
    ext i j
    have hp:=congr_fun (he j) i
    simpa only [mulVec_single_one,col_apply,Pi.single_apply,one_apply,eq_comm] using hp
lemma polar : H.paint z⁻¹*H.paint z=1:=by simpa only [inv_inv] using H.cups z⁻¹
lemma inverse : (H.paint z)⁻¹= H.paint z⁻¹:= Matrix.inv_eq_right_inv (H.cups z)

-- column/row sums actually over *one* color block ONLY. enumerate pick first.
omit [DecidableEq X] in
lemma select (x:X) (f:X→ℝ) (h:∀ j:X,H.room j ≠ H.room x → f j=0) : ∑ j,f j = ∑ i:G.ColorIndex,f (H.pick x i):=by
   classical
   let e:G.ColorIndex ↪ X:=⟨H.pick x,fun i j hi=> ((H.ink_pick x i).symm.trans (congr_arg H.ink hi)).trans (H.ink_pick x j)⟩
   let s:=Finset.univ.map e
   have hh i (he:H.room i=H.room x): i∈s:= by
     have hz:H.pick x (H.ink i)=i:= (H.pickable he.symm _).trans (H.pick_self i)
     exact Finset.mem_map.mpr ⟨_,Finset.mem_univ _, hz⟩
   exact (Finset.sum_subset (Finset.subset_univ s) (fun i _ hi=> h _ (fun hp=>hi (hh i hp)))).symm.trans (Finset.sum_map ..)
lemma pins {α':Type*}[Fintype α'] (A:Matrix X α' ℝ) (i:X)(j:α') :
    (H.paint z*A) i j=∑ p:G.ColorIndex,H.paint z i (H.pick i p)* A (H.pick i p) j:=
    H.select i (fun a=>H.paint z i a * A a j) (fun a h=>by rw [H.tone _ i _ h.symm,zero_mul])
lemma paws {α':Type*}[Fintype α'] (A:Matrix α' X ℝ) (i:α')(j:X) :
    (A*H.paint z) i j=∑ p:G.ColorIndex,A i (H.pick j p) * H.paint z (H.pick j p) j:=
    H.select j (fun a=>A i a * H.paint z a j) (fun a h=>by rw [H.tone _ a j h,mul_zero])
end Hive

-- body on plain entire X

def family (α:Type*) (G:Gauge): Hive G (α×G.ColorIndex) α:= ⟨Embedding.refl _,fun i j=>(i.1,j),fun _ _=>rfl⟩
end YM.Planned.PrimaryIntegral295.Hives
