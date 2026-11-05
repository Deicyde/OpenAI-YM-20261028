import YM.Extra.SOURCE_HISTORIES.Reserve
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Layering
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Tissue
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Weaves
import YM.Progress.CLASSICAL_KIN_RECURSION.Descend
import YM.Push.RELAY_DIFFERENCE.Shuffles
import YM.SectorNext.VACUUM_NORMALIZATION.Pivots
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Hosted

/-!
# Unmarked progression on Soft stretch

Not assuming the whitened representation can push! Still have/need exact
unnormalized equality against the real (soft) densities, before any final
marker test.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Filter MeasureTheory Finset Lattice Wilson RG Precision
open Pressure Push.SectorMeasure Next.Rank RankCovariance Thirst  Ac Baler Glyph Tapes Marker
open Display Display.Docking Display.Sew Value Flux SectorNext.Vacuum
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {ι α : Type} [Fintype ι] [Fintype α] {σ d δ e k x : ℝ}

section stage
variable {O : Teller G} {T : Tube G S} {L : Lantern G S} (R : Rep G f) (Q : Rep G c)
  (p : ι→ Zest G S x L.park Q.p.threshold) (A : Boosted T O x)
  (hs : 25*radiusB x+30 ≤ Q.p.B) {o ℓ g r η M l y w : ℝ} (hR : Tissue R o ℓ g r η)
local notation "P0" => white R
local notation "R0" => Gel.archived P0 (blank f) hR.status
local notation "E1" => (Empty.elim : Empty→SourceAt G (blank f))
local notation "Fl"=> (Empty.elim : Empty→Flake S G x L.park (blank c) Q.p.threshold)
local notation "X0"=> unmarked P0 Q p A hs (blink S) hR.status
local notation "G0"=> germ X0 A
-- shadow with same K,p indeed sufficient for dust reconstruction
include hR
lemma pale {W θ} [Fintype W] [DecidableEq W] [IsEmpty ι] (H : ι→ SourceAt G θ) (K : α → Lifted G θ R.p.threshold) (he : Background R K) (hp : ∀ i,(K i).fires=quiet W) : Value.dust R H K= (scalar W) ∘ R.eval:= by
  funext U; change _= scalar W _
  rw [whiteDust,darkDust P0 hR.status H K he hp, Function.comp_apply,whiteDensity R U,map_mul,Algebra.smul_def]; rfl
include A
lemma white_empty (U : Config G c) : S.push R.beta (Value.dust R E1 R0) U= scalar Empty (S.push R.beta R.eval U):= by
  rw [pale R hR _ _ (conservation P0 (blank f) hR.status) (fun _=>rfl)]
  let f:= LinearMap.toContinuousLinearMap ({ toFun:=scalar Empty, map_add':=map_add _,map_smul':=fun z x=>by change scalar _ (z * x)=_; rw [map_mul]; exact (by rw [RingHom.id_apply,← Complex.coe_smul,Algebra.smul_def]; rfl) } : ℝ →ₗ[ℝ] veil Empty)
  have h : Integrable _ _:= StepData.push_slice (S.isKernel A.produced.branched R.beta) U _ ((payEnv R hR).integrable _)
  unfold StepData.push; change _= f _; rw [← f.integral_comp_comm h]; exact integral_congr_ae (Filter.Eventually.of_forall fun x=> (f.map_smul ..).symm)
variable {D : Allocation G S x w} {J : ChartRatio G} (ν : Config G c→ℝ)
    (he : Veins (white R) Q p A hs hR.status e M l σ) (Ly : Lease S.patch.L R.p Q.p e M l σ y η) (hz : BodyGrant T R L D J Q.p.threshold p (fun V=> (↑(ν V):ℂ)))
    (h : Coupler T L J D R.beta)
include hz h Ly he
lemma grain_holds :
    S.push R.beta (Value.dust R E1 R0)=
       bouys (Q:=Q) (fun x=>↑(ν x)) G0 (bequeath X0 A):= by
  obtain ⟨z,v,hς,_⟩:= v_commissioned P0 Q p A hs hR.status he (blank f) (blank c) (blink S) Ly (fun _=>1) (fun _=> zero_lt_one)
  let C:=picture R Q p R0 Fl A hs (blink S)
  have ha : earns_layout C T:= fun i U H k=> (refund _ _ _ _ _ _ _ _ _ _ _ _ hς (fun _=> zero_lt_one) Ly.lamps Ly.bright i U k H).1
  have ht' : Light R E1 R0 (fun _=>1) R.p.supportExponent 0 η := ⟨⟨fun _=>0, (fun i=>i.elim),fun i=>i.elim⟩,sticker P0 _ hR.status _⟩
  funext i; have hπ:=brigade A Q C i (fun x=>↑(ν x));
  refine (rendered C (Λ:=fun i=> (↑(ν i):ℂ)) (dustEnvelope R E1 R0 hR (fun _ => zero_lt_one) R.p.exponent_pos.le ht' (conservation P0 (blank f) hR.status)) (dustMoves R E1 R0 hR) A h ?_ ha i).trans ?_
  swap; exact (show _ from hπ)
  exact fun A' V hv=> stage_gain R Q p R0 Fl A hs (blink S) E1 (by intro V A' k z; rw [Fintype.sum_empty,Next.Rank.Exponential.pass_zero,Fintype.prod_empty]) hz V hv
variable (E:α→Rim Q.p.threshold G c) (hp : Resin (white R) Q p A hs hR.status ν E e y)
local notation "Z"=> germinates P0 Q p A hs hR.status E
local notation "Z0"=> v_carves P0 Q p A hs hR.status E he (blank f) (blank c) (blink S)
include hp
lemma made_soft {ό θ c0 d v : ℝ} (hX : Tissue Z ό θ c0 d v) : (Z).eval=S.push R.beta R.eval:= by
  obtain ⟨hT,hV⟩:= v_in_boxes P0 Q p A hs hR.status E he (blank f) (blank c) (blink S) Ly hp (fun _=>1) (fun _=>zero_lt_one)
  let D':= bequeath X0 A; let K:= Z0
  have hC : Matric K D' (S.push R.beta (Value.dust R E1 R0)):= by
    have hX : S.push R.beta (Value.dust R E1 R0)= bouys (Q:=Z) (fun x=>↑(ν x)) G0 D':= grain_holds R Q p A hs hR ν he Ly hz h -- dependent Matric!
    rw [hX]; exact in_bulk _ _ _ _ hT.pays hT.rolls
  let U(i : Inn X0):Prop := False
  obtain ⟨H,H'⟩:= sunny_pass K D' _ hC U
  let F:= Sum.elim (downstairs K D' U) (upstairs K D' U); let Y:=after D' (measureH K) K.pay
  have htS (i) : (Y i).fires=quiet _:= by
    apply Subtype.ext; ext z; exact z.elim
  let X:= Bottom K D' U ⊕ Top K D' U
  haveI : IsEmpty X:=⟨fun t=> by obtain ⟨x,h⟩:= (F t).chosen; exact x.elim⟩
  have hv' : S.push R.beta (Value.dust R E1 R0)= (scalar Empty) ∘ (Z).eval:= Eq.trans H (pale Z hX F Y H' htS)
  ext1 i; apply scalar_inj Empty; rw [← show _=scalar Empty ((Z).eval i) from congr_fun hv' i]; exact white_empty R A hR i
end stage
end YM.PhysicalNext.InteractingRank.Soft
