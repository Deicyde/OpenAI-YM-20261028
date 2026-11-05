import YM.WilsonBulk.Build.Accept

/-!
# Finite output equation for all admissible real-germ transforms

Use for Ward, affine-null projection of rank2, and tree/tag independence.
Complete (through every coefficient), even when additive stopped at any
finite order. This output is positive M̂ including branch scalar cumulants.
We start relative reset subtracting only field-independent output (proved
coherent with zero expectation later on cashless cover). Domain chart.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Atelier
open Function Filter Matrix Sheet Precision RG Exterior Lattice Wilson FreeResolvent
open Stationary (Army)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open Coursing
variable {α β κ ι : Type} [Fintype κ] [Fintype ι]
variable {G : Gauge} {c f n : Side} {S : StepData c f} {F L : Coursing ι S} {P Q : Bed} {J : ChartRatio G} {a : ℝ} {k : G.El}
variable {M N : Logbook G f} {W Z : Logbook G c} {t r : S.Choices}
variable (s : Signed) (b : Site c)

def plateau (J : ChartRatio G) (P : Bed) (t : S.Choices) (F : Coursing ι S) (M : Logbook G f) (W : Logbook G c) :=
    glimmer G ι P F (auditorium S t M) (haarTape c f J) W
abbrev pressurize (Q : Bed) (W : Logbook G c) := grains (matrixK G c Q)-W
lemma ride_preserve {u v : Tabletop κ→Interface G c} {X : Tabletop κ→Site c→ G.El} (hl : Bid.Larger (G:=G) S) (hc : Consoles P Q S) (hb : 0<a) (hB : Ticket a f P) (hJ : LocalRatio J)
    (h : Plays s b u v X) (hf : plateau J P t F M W) (hg : plateau J P r L N Z) (hh : Dances N) (hw : Spins s (S.ratio.embed b) M N) :
    submit (exposure u) (pressurize Q W)=submit (exposure v) (pressurize Q Z) := by
  let θ:= lands (festival s b X) F L P u v
  have h₁:= recipe G (F:=F) hB hb hl hc (exposure u) hf
  have h₂:= recipe G (F:=L) hB hb hl hc (exposure v) hg
  dsimp only at h₁ h₂; rw [← porch_code _ h.source h.quiet] at h₁
  rw [← porch_code _ h.ends h.sitting] at h₂
  have he := moving (F:=F) (L:=L) (P:=P) s b r t hl.1 h hh hw
  have ha := starts_of h₁ h₂ he
  obtain ⟨k,hk⟩:= h.encores
  have hh : Legible (festival s b X) F P u:= parades s b h.source h.val hk
  obtain ⟨V,H, hV⟩:= quill_derive θ (lands_jet _ _ _ _ _ _ h.quiet h.ends hh)
  obtain ⟨hv,hz,hf',hs⟩ := Steps_derive (exposure θ) hV (F.confines G P hB) (L.confines G P hB) (F.prepared G hl hb P hB) (L.prepared G hl hb P hB) ha
  have hu := fee_received (L:=L) F P u v h.source h.quiet h.ends h.sitting J hJ (festival s b X) hh (V:=V) hs
  simp only [pressurize,map_sub]; exact equated hs hz hv hf' (F.confines G P hB) (F.prepared G hl hb P hB) (F.short_law G P hB) h₁ h₂ he hu
lemma costumed_once {v : Tabletop κ→Interface G c} (h : ContDiffAt ℝ ω v 0) (he : v 0=0) : Plays s b v (swivel s b ∘ v) (fun _=>1) := by
  refine ⟨h,(swivel_jet ..).contDiffAt.comp _ h,he,by rw [Function.comp_apply,he,swivel_birth],⟨1,rfl⟩,Stationary.Army.park _ _, Eventually.of_forall fun z=>?_⟩
  rw [Function.comp_apply,swivel_sign]; exact (turn_person _).symm
lemma costumed_coarse (k : G.El) :
    Plays 1 (0:Site c) (upper (Pennant G c) (Needle G c)) (pigment c k) (curtainK c k ∘ lower _ _) := by
  let U:= upper (Pennant G c) (Needle G c); let A:=lower (Pennant G c) (Needle G c)
  refine ⟨U.contDiff.contDiffAt,pigment_jet _,map_zero U,pigment_birth _,⟨k,by rw [Function.comp_apply,map_zero, curtainK_zero]⟩,weatherK k A.contDiff.contDiffAt, (pigment_laid k).mono fun z hz=>?_⟩
  rw [pull_id]; exact hz
lemma spins_post (hl : Bid.Larger (G:=G) S) (hc : Consoles P Q S) (hb : 0<a) (hB : Ticket a f P) (hJ : LocalRatio J) (hf : plateau J P t F M W) (hg : plateau J P r L N Z) (hh : Dances N) (hw : Spins s (S.ratio.embed b) M N) :
    Spins s b (pressurize Q W) (pressurize Q Z) := by
  have h:= ride_preserve s b hl hc hb hB hJ (costumed_once s b (v:=id) contDiffAt_id (id_eq _)) hf hg hh hw
  rw [comp_id,exposure_id,submit_id] at h; exact h.symm
lemma dances_post (hl : Bid.Larger (G:=G) S) (hc : Consoles P Q S) (hb : 0<a) (hB : Ticket a f P) (hJ : LocalRatio J)
    (hf : plateau J P t F M W) (h : Dances M) : Dances (pressurize Q W) := fun k=> by
  have h:= ride_preserve 1 0 hl hc hb hB hJ (costumed_coarse k) hf hf h (by rw [show S.ratio.embed 0=0 from S.ratio.root.map_zero]; exact spins_id _)
  rw [upper_code] at h; exact h.symm
lemma tree_credible (hl : Bid.Larger (G:=G) S) (hc : Consoles P Q S) (hb : 0<a) (hB : Ticket a f P) (hJ : LocalRatio J)
    (hf : plateau J P t F M W) (hg : plateau J P r L M Z) (hh : Dances M) : W=Z := by
  have h := spins_post 1 0 hl hc hb hB hJ hf hg hh (by rw [show S.ratio.embed 0=0 from S.ratio.root.map_zero]; exact spins_id _); unfold Spins at h; rw [swivel_id, exposure_id,submit_id] at h; exact (sub_right_inj.mp h).symm
omit [Fintype ι] in
lemma planar_read (hl : S.patch.Branches S.kernel G) {H : Record (Chamber (Pennant G f) (Pennant G c))} (hF : FrameBound H) (hf : Free H) (h : Based H) (hJ : LocalRatio J) (hA : Steps 1 M (grains (matrixK G f P)))
    (ht : volumeTape H= curtain (matrixK G f P) (probeX G S) S.kernel.penalty (auditorium S t M) (haarTape c f J)) :
    plateau J P t F M (ruling (predictor G F.tree P) (volumeTape (receive (house (regionJ G F.tree P)) H false))) := script_ready _ _ hF hf h (haar_empty hJ) (auditorium_start t hl hA) ht
end YM.WilsonBulk.Atelier
