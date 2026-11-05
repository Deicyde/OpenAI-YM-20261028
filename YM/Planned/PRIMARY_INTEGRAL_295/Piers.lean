import YM.Planned.PRIMARY_INTEGRAL_295.Novas
/-!
# Strict output region extension, for single canonical call

Open around True physical T.S footprint guides. Larger x thresholds and period
require numerical commitment; no resolving Evaluate.T.Exact of Kernel on all V by
extension. Measures U actual tested. o.Lattice order arbitrary held. Hull.W
for Φ.W integrations, frame choices across pulls coherence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Piers
open Function Filter Set Metric MeasureTheory ProbabilityTheory Matrix Finset
open Lattice RG Wilson Pressure Labels Source Precision Exterior Tree Carrier Bloch Progress.StationaryScenes Bazaars Launch Shapes
open Villa Floor Glints Fizz Fizz.Gush Little Density Little.Core Push.Uniform Sparks Night Barges Novas Novas.Torch Mansions  Castles  
open Icebergs Tropics Kelps Nimbuses Streets Dawning Cabins Cedar Next.Fluctuations Racks Dials WardBin.Lies
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {G:Gauge} {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k r n d χ:ℕ} {c f:Side} {t θ ξ C M s : ℝ}
variable {F:Labels.Frame G d} {S:StepData c f}

section Space
def focus (r:ℕ)(c:Side):Support c:= Lattice.halo (r+1) {0}
lemma inhabit (y:Site c): y∈focus r c ↔ separation 0 y ≤ r+1:=by simp [focus,halo_spec]

def Zone (c:Side)(G:Gauge)(r:ℕ)(θ:ℝ) := {V:Config G c | ∀ i:Cell c,¬Disjoint (touched i) (focus r c) → G.chord (faceValue V i)<2*θ}
lemma zone_space : IsOpen (Zone c G r θ):= by
   have h : Zone c G r θ = ⋂ i:Cell c, if Disjoint (touched i) (focus r c) then Set.univ else {V:Config G c | G.chord (faceValue V i)<2*θ}:= by ext V; simp only [mem_iInter,Zone,Set.mem_setOf]; apply forall_congr'; intro p; split <;> simp_all
   rw [h]; refine isOpen_iInter_of_finite fun i=>?_ ; split
   · exact isOpen_univ
   unfold faceValue; exact isOpen_lt (by fun_prop) continuous_const


lemma zone_anchor (V:Config G c) (h:V∈Zone c G r θ): Healthy (2*θ) (focus r c) V:=by
   refine Finset.disjoint_left.mpr ?_; intro i hh hy
   obtain ⟨p,hp,hx⟩:= (flags_spec ..).mp hy; have ha:= h p (Finset.not_disjoint_iff.mpr ⟨_,hp,hh⟩); linarith


end Space

-- budget for strict region U.Increase. single.K of K.n order.
structure Spark (K:Knurls G k)(c:Side) (r:ℕ)(θ t M:ℝ):Prop where
   positive : 0<θ ∧ 0<t
   ncost : 1≤k
   height : 2*(r+1) < c.val
   vent : let v:= 4*(1+(r:ℝ))*(hcount*(2*θ)); v ≤ K.r ∧ t⁻¹*(K.C*v) ≤ M

section Little
-- any path artist over one true setback. takes ContinuityAt generic or increment.ALL.
variable (o:Lattice.Order)(K:Knurls G k)(U:Config G c) (hs:U∈Zone c G r θ) (he: Spark K c r θ t M)
include he hs
lemma ambient (i:Bond c) (hi:separation 0 i.1 ≤ r): G.chord (Lattice.gauge (cardAt o U) U i) ≤ 4*(1+(r:ℝ))*(hcount*(2*θ)):=by
    have hp:=he.positive.1
    have ht:=Racks.costs o (r+1) he.height (focus r c) (fun x ha=>(inhabit x).2 ha) (2*θ) (by positivity) U (zone_anchor U hs) i (Nat.lt_succ_of_le hi)
    apply ht.trans
    have ha :0≤hcount*(2*θ):=by have :=hcount_pos; positivity
    gcongr
    exact le_rfl
omit [NormedSpace ℝ E] in
lemma shines (X : E→ Config G c)(hf:X 0=U)(hh:ContinuousAt X 0):
   let b:=patched t (cardAt o U) r X; ‖b 0‖≤ M ∧ ∀ᶠ y in 𝓝 0, AgreeNear id 0 r (Lattice.gauge (cardAt o U) (X y)) (represent (t • b y)) :=by
   intro b
   have hx:= he.vent; let C:=4*(1+(r:ℝ))*(hcount*(2*θ)); have ha:= K.cap; have hz:= hcount_pos; obtain ⟨hθ,hτ⟩:=he.positive; have hu:0≤C:=by unfold C; positivity
   have hr : 0≤M:=le_trans (show 0≤t⁻¹*(K.C*C) from by positivity) hx.2
   let z:=cardAt o U
   have hc (e:Bond c)(hi:separation 0 e.1 ≤ r): G.chord (Lattice.gauge z (X 0) e) ≤ C:= by rw [hf]; exact ambient o K U hs he e hi
   constructor
   · apply (pi_norm_le_iff_of_nonneg hr).2; intro i; obtain ⟨i,rfl⟩:= (Work.E03.poleEquiv c).surjective i
     unfold b; rw [symbolic]; unfold room; split<;>rename_i h
     · have hS:= hc i h
       rw [norm_smul,Real.norm_of_nonneg (by positivity : 0≤t⁻¹)]
       have hg:= (K.sparks _ (by exact hS.trans (hx.1.trans (by linarith [K.opening])))).2
       exact (mul_le_mul_of_nonneg_left (hg.trans (mul_le_mul_of_nonneg_left hS (by linarith))) (by positivity)).trans hx.2
     rwa [norm_zero]
   have hp:=bridle t z r X K hτ (fun i hi=>?_)
   · filter_upwards [hp] with x hp i hi; exact (hp i hi).1
   have hc': ContinuousAt (fun y=> G.chord (Lattice.gauge z (X y) i)) 0 :=by
       unfold Lattice.gauge; exact G.continuous_chord.continuousAt.comp ((continuousAt_const.mul ((continuousAt_pi.mp hh) i)).mul continuousAt_const)
   have hl: G.chord (Lattice.gauge z (X 0) i) ≤ K.r:=(hc i hi).trans hx.1
   exact hc'.eventually (ge_mem_nhds (by linarith [K.opening]))

-- rough Spot along EVERY En inc path proof, k>0.
lemma traveled : ContDiffAt ℝ k (patched t (cardAt o U) r (increment U)) 0 :=by
    cases k with
    | zero => have hh:=he.ncost; omega
    | succ k =>
      let z:=cardAt o U
      apply contDiffAt_pi.mpr; intro i; obtain ⟨i,rfl⟩:= (Work.E03.poleEquiv c).surjective i
      simp_rw [symbolic]; unfold room; split <;> rename_i h
      swap; · exact contDiffAt_const
      let W:= Lattice.gauge z U i
      have ht := ambient o K U hs he i h
      have hW : G.chord W≤K.r:= ht.trans he.vent.1
      obtain ⟨hF,hG⟩:= K.helps W hW; let D:=G.plog (G.mat W)
      let f(y:Directions G c):Drum G (k+1) := (Pi.single (0:Fin (k+1)) (G.adjoint (z i.1) (y i)), D)
      have hf : f 0=(0,D):=by simp [f]
      have hD:= (K.sparks W (hW.trans (by linarith [K.opening]))).1
      have hy : ContDiffAt ℝ (↑(k+1:ℕ)) f 0:= by
         apply ContDiffAt.prodMk _ contDiffAt_const; apply contDiffAt_pi.mpr; intro j; simp_rw [Pi.single_apply]; split
         · exact (G.adjoint (z i.1)).toContinuousLinearMap.contDiff.contDiffAt.comp _ (contDiffAt_pi.mp contDiffAt_id i)
         exact contDiffAt_const
      have hz := ((show ContDiffAt ℝ (↑(k+1:ℕ)) (forge G (k+1)) (f 0) from hf.symm ▸ hF).comp _ hy).const_smul t⁻¹
      apply hz.congr_of_eventuallyEq; apply Eventually.of_forall; intro y
      apply congr_arg; apply congr_arg G.plog; apply congr_arg G.mat
      let v:= G.adjoint (z i.1) (y i)
      change Lattice.gauge z (increment U y) i= chant G _ (Pi.single 0 v)*G.lieExp D; rw [show G.lieExp D=W from hD]
      have hh (p:Fin k):Fin.tail (Pi.single 0 v:Fin (k+1)→G.Color) p=0:=by simp [Fin.tail]
      rw [show chant G (k+1) (Pi.single 0 v)=G.lieExp v from ?_];
      · have he (x:G.El)(v:G.Color):G.lieExp (G.adjoint x v) = x*G.lieExp v*x⁻¹:=by apply G.mat_injective; simp [G.mat_adjoint,G.exp_conjugate]; rfl
        unfold v; rw [he]; unfold W Lattice.gauge increment; group
      change chant G k (Fin.tail (Pi.single (0:Fin (k+1)) v : Fin (k+1) → G.Color)) * G.lieExp ((Pi.single (0:Fin (k+1)) v: Fin (k+1)→ G.Color) 0)= _
      rw [show Fin.tail (Pi.single (0:Fin (k+1)) v : Fin (k+1)→ G.Color)= (0:Fin k→G.Color) from funext hh,(chant_pc G k).2]; simp
end Little
end YM.Planned.PrimaryIntegral295.Piers
