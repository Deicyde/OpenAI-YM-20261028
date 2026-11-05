import YM.Planned.PRIMARY_INTEGRAL_295.Decks
/-!
# Smooth pay~χ C law at ONE constant application base near cone

No chronology from Prepare yet. Uses radius and *value* conditions for
constant closet Certification.Bank. Then earns hurried ContDiffAt upstream
for even unrestricted Env through this step (no price estimates until Charter/reapply
path affine). C.Hessian d-v log earned at v0 only to pay invert & continuity.
No pretending task Era convolution.`T.step Pass`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Ritual
open Function Filter Set Metric MeasureTheory ProbabilityTheory Matrix Finset
open Lattice RG Wilson Pressure Labels Source Precision Exterior Tree Carrier Bloch Progress.StationaryScenes Bazaars Launch Shapes
open Villa Floor Glints Fizz Fizz.Gush Little Density Little.Core Push.Uniform Sparks Night Barges Novas Novas.Torch Mansions Decks Castles
open Icebergs Tropics Kelps Nimbuses Streets Dawning Cabins Cedar Next.Fluctuations
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {G:Gauge} {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k r n d χ:ℕ} {c f:Side} {t ξ C M s : ℝ}
variable {F:Labels.Frame G d} {S:StepData c f} {Q:Teller G}
variable (P:Torch G S)

structure Relic (Q:Teller G) (T:SectionData F)(r k χ:ℕ)(C t M s:ℝ):Prop where
   deck : Deck P T r k χ C
   price : Mansions.Cost (dough S.patch Q k) G S.ratio.count t C M s P.R k χ
   stage : t*M < trust S.patch S.kernel G
   rings : ∃ H H', Rails.Ringlets Q P.tube H H'
   sizing : Bid.Larger (G:=G) S

variable {T:SectionData F} (h:Relic P Q T r k χ C t M s)
include h
lemma punch {v:Dir G c}(hv : ‖v‖ ≤ M): ‖t • v‖≤(dough S.patch Q k).radius ∧ ‖t • v‖< trust S.patch S.kernel G:=by
   have ht:=h.price.plate.1.1
   have he: ‖t • v‖ ≤ t*M:=by rw [norm_smul,Real.norm_of_nonneg ht.le]; exact mul_le_mul_of_nonneg_left hv ht.le
   exact ⟨he.trans h.price.plate.2,he.trans_lt h.stage⟩
lemma bath (b:E→Dir G c)(hb:Ember k b M): let Z:= berth P b t
    Charter C t P.core Z T.stencil k χ ∧ Z.Service T.stencil P.tube.R.A0 ((dough S.patch Q k).paid G S.ratio.count k) k χ C s:=by
   intro Z; have he:= (punch P h hb.2.value).2
   have hf:∀ᶠ y in 𝓝 (0:E), ‖t • b y‖≤trust S.patch S.kernel G:= (hb.1.continuousAt.const_smul t).norm.eventually (ge_mem_nhds he)
   have hx := dance P b t h.deck hf h.sizing.1
   exact ⟨hx,Mansions.baths Z hb hx (dough_done P.core _ _ h.rings h.sizing) h.price⟩
omit [NormedSpace ℝ E] in
lemma ceremony (b:E→Dir G c)(hb:‖b 0‖≤M) : let Z:= berth P b t; let H:= pose P b t
    Clear (H.C 0) (Post.bark k C) ∧ ∀ i:P.Index, let A:=P.clan.homes.chamber i (Z.foyer 0); A*A⁻¹=1 :=by
   intro Z H
   let x:ℝ→Dir G c := fun _=>b 0; let v:= pose P x t; let B:=berth P x t
   have hf: Ember k x M:= Ember.weakening (Ember.constant ..) hb
   have hx := (bath P h x hf).2
   have hz:= (B.remitted hx le_rfl).clear
   refine ⟨hz,fun i=>?_⟩
   intro A; exact (Windows.Glaze.attends B.homes hx.tests.toGlaze i).1
section Diff
variable (b:E→Dir G c)(hb:‖b 0‖≤M)(ht:ContDiffAt ℝ k b 0)
include hb ht
private lemma dot_v (i j:(berth P b t).hub): let Z:= berth P b t
    ContDiffAt ℝ k (fun v=>Z.foyer v i j) 0 ∧ ContDiffAt ℝ k (fun v=> Z.ash v i) 0 :=by
   let K:=P.core; let v (y:E):=t • b y; have hp:=h.price
   let H:= dough S.patch Q k; have hz : Quantum K H P.tube.R.A0 k:= dough_done P.core _ _ h.rings h.sizing
   have hx: ‖v 0‖≤ H.radius:= (punch P h hb).1
   have hv: ContDiffAt ℝ k v 0:=ht.const_smul t
   have hd i j : ContDiffAt ℝ k (fun y:E=> K.D (v y) i j) 0:=((hz.drums i j _ hx).analytic.of_le le_top).comp _ hv
   have hf i : ContDiffAt ℝ k (fun y:E=> K.F0 (v y) i) 0:=((hz.hands i _ hx).analytic.of_le le_top).comp _ hv
   refine ⟨?_,?_⟩
   · exact (ContDiffAt.sum (s:=Finset.univ) (fun a _=>(hd a i.val).mul (hd a j.val))).add (contDiffAt_const (c:=K.fires i.val j.val))
   exact (ContDiffAt.sum (s:=Finset.univ) (fun a _=> (hd a i.val).mul (hf a))).const_smul t⁻¹
private lemma rose (i:P.Index) (j:P.clan.grounds):ContDiffAt ℝ k (fun y:E=>P.clan.homes.reed ((berth P b t).foyer y) i j) 0:=by
    classical
    let w:= P.clan.homes.W i; let f(v:E):Matrix w w ℝ:=P.clan.homes.chamber i ((berth P b t).foyer v)
    have he(p q:w) :ContDiffAt ℝ k (fun y=> f y p q) 0:= (dot_v P h b hb ht p.val q.val).1
    have hh := (pass_mood he ((ceremony P h b hb).2 i)).1
    simp_rw [Windows.reed]; split <;> rename_i hq
    · exact hh ⟨j,hq⟩ _
    exact contDiffAt_const

lemma blossom : let Z:=pose P b t
    ContDiffAt ℝ k (MapB P.Index ∘ Z.C) 0 ∧ ContDiffAt ℝ k Z.mean 0 :=by
   let I:=P.Index; let H:= berth P b t; let x:=P.clan.homes; intro Z
   have he (i j:P.Index):ContDiffAt ℝ k (fun y:E=> Z.C y i j) 0:=by
      have hx := rose P h b hb ht
      exact contDiffAt_const.mul ((hx i (P.clan.bee j)).add (hx j (P.clan.bee i)))
   constructor
   · have he': (MapB P.Index)∘Z.C = fun y=> ∑ i,∑ j,Z.C y i j • MapB P.Index (Matrix.single i j 1):=by
          let A (y:E):Matrix P.Index P.Index ℝ:= Z.C y;
          have h(A:Matrix P.Index P.Index ℝ): MapB P.Index A= ∑ i:P.Index,∑ j:P.Index,A i j • MapB P.Index (Matrix.single i j 1):=by
            simp_rw [←map_smul,←map_sum] 
            apply congr_arg (MapB P.Index ·); apply Matrix.ext (m:=P.Index) (n:=P.Index); intro (i : P.Index) (j : P.Index); simp [Matrix.sum_apply,Matrix.single,ite_and]
          funext y; exact h (A y)
     rw [he']; exact ContDiffAt.sum fun i _=> ContDiffAt.sum fun j _=> (he i j).smul contDiffAt_const
   let f (y:E) := P.muster (stepped P.core b t y) (patchedAt P.core b t y)
   have he (i:P.Index) : ContDiffAt ℝ k (fun y=> f y i) 0:= ContDiffAt.neg (ContDiffAt.sum (s:=Finset.univ) (fun j _=> (rose P h b hb ht i j).mul ((dot_v P h b hb ht j j).2)))
   have hf : ContDiffAt ℝ k f 0:=by
      let L:= PiLp.continuousLinearEquiv 2 ℝ (fun _ : P.Index => ℝ) -- name?
      have hx : ContDiffAt ℝ k (fun y=> WithLp.ofLp (f y)) 0:=contDiffAt_pi.mpr he
      exact L.symm.contDiff.contDiffAt.comp _ hx
   exact P.mist.contDiff.contDiffAt.comp _ hf
end Diff
end YM.Planned.PrimaryIntegral295.Ritual
