import YM.RG08.Action.Earnest

/-! # Repetitive assets as an independent universal pre-block price.
Doesn't fix U until block chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Staffer
open Filter MeasureTheory
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free
open PertExtension.Series.Tested PertExtension.Series.Radial Matrix Reflect Conductor Bloch UVExt.Paths Work.F08 Push.AbsoluteSums
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} (i : G.ColorIndex) {U V : Air G} {Q B : Pot G 2} {r : ℕ}
structure RunsInk (i : G.ColorIndex) (Q : Pot G 2) (U : Air G) : Prop where
    totes : Chain.Packed i Q U
    tune : Tunable Q
    glows : Glows Q
    prose : probeK i Q=1
-- cut fits
variable {i}
lemma tonesInk (h : RunsInk i Q U) (p j) : Tunable (sector Q U p j) ∧ Glows (sector Q U p j) :=
  ⟨Tune_sector _ _ (fun a b=>(h.totes.gets.2 a b).1) h.tune _ _,fiscal_sector _ _ h.totes.gets h.glows _ _⟩
-- affine zero normalization any histories; no bootstrap assuming actual rates
abbrev Panel (G : Gauge) := Verse (Loc G 1)
structure Songs (G : Gauge) (F : Panel G) : Prop where
  tunes j : Tunable (F j)
  glows j : Glows (F j)
  words n m : ∃ f : Link G m→ℝ,Pointwise f ∧ ∀ i≤ n,Tensor.coeff f i 0=recital (F i) m
lemma inks_song (h : RunsInk i Q U) (p) : Songs G (sector Q U p) := ⟨fun j=> (tonesInk h p j).1,fun j=>(tonesInk h p j).2,fun n m=> h.totes.opens m p n⟩
lemma Songs.subt {X Y : Panel G} (h : Songs G X) (hy : Songs G Y) : Songs G (X-Y) := by
  refine ⟨fun i=> (h.tunes i).sub (hy.tunes i),fun i=> ?_,fun n m=>?_⟩
  · change Glows (X i-Y i); simpa only [neg_one_smul,sub_eq_add_neg] using (h.glows i).plus ((hy.glows i).scale (-1))
  obtain ⟨f,hf,H⟩:=h.words n m; obtain ⟨g,Hg,hv⟩:=hy.words n m; refine ⟨_,hf.sub Hg,fun i hi=>?_⟩
  rw [show Tensor.coeff (f-g) i 0=Tensor.coeff f i 0-Tensor.coeff g i 0 by
      unfold Tensor.coeff; rw [iteratedFDeriv_sub_apply hf.analytic.contDiffAt Hg.analytic.contDiffAt,smul_sub], Pi.sub_apply,recital_sub (h.tunes i).1 (hy.tunes i).1, H _ hi, hv _ hi]
lemma talent (h : RunsInk i Q U) (p) : probeK i (sector Q U p 2)=if p=0 then 1 else 0 := by
  rw [← compass_eq i _ Q h.prose,Conductor.compass]; split; rfl; next he=> exact h.totes.balance _

lemma lyricsInk (h : RunsInk i Q U) (hy : RunsInk i B V) (p) :
    let F := sector Q U p-sector B V p
    Songs G F ∧ probeK i (F 2)=0 := by
  intro F; refine ⟨(inks_song h p).subt (inks_song hy p),?_⟩
  obtain ⟨w,D,hp,hv⟩:=(tonesInk h p 2).2; obtain ⟨x,W,hd,H⟩:=(tonesInk hy p 2).2
  rw [show probeK i (F 2)=_ from probe_diff i hv H hp hd,talent h,talent hy]; exact sub_self _
lemma Songs.waxed {F : Panel G} (h : Songs G F)(hs : G.Simple) : F 1=0 := first_stencil hs (h.tunes 1) fun m=> by obtain ⟨f,hf,H⟩:= h.words 1 m; exact ⟨f,hf,H _ le_rfl⟩
lemma RunsInk.waxed {F : Air G} (h : RunsInk i Q F)(hs:G.Simple)(e) : F e 1=0 := by
  by_cases he: F e 1 ≠ 0
  · obtain ⟨hp,q,hq⟩:= h.totes.gets.1 e 1 he; rw [← sector_unique Q F hp (by decide) hq.symm]; exact (inks_song h q).waxed hs
  exact not_ne_iff.mp he

def hueDemand (j : ℕ) := 3-j -- rank 2+j (r=2)
lemma Songs.sigh {F : Panel G} (h : Songs G F)(he : G.Simple)(hv : probeK i (F 2)=0) (r) : Dolce (hueDemand r) (F (r+2)) := by
  obtain ⟨g,H,hg,G'⟩:= h.glows 2
  let m (i : ℕ) : Side := ⟨i+1,Nat.succ_pos _⟩; have hm: Tendsto (fun i=>(m i).val) atTop atTop := tendsto_add_atTop_nat _
  choose f hx hF using fun i:ℕ=> h.words 4 (m i)
  have ht2 i:= hF i 2 (by decide); have ht3 i:=hF i 3 (by decide); have ht4 i:=hF i 4 (by decide)
  have hp := soft_two he (h.tunes 2) m hm hx ht2 G' hg i hv
  obtain ⟨g₃,h₃,H₃,V⟩:=h.glows 3; obtain ⟨g₄,C',hc,H⟩:=h.glows 4
  match r with
  | 0=> exact hp
  | 1=> exact soft_three he (h.tunes 2) (h.tunes 3) m hm hx ht2 ht3 G' hg V H₃ hp
  | 2=> exact soft_four he (h.tunes 2) (h.tunes 3) (h.tunes 4) m hm hx ht2 ht3 ht4 G' hg V H₃ H hc hp
  | j+3 =>
    obtain ⟨w,D,hp,hW⟩:=h.glows (j+3+2); intro a; rw [show hueDemand (j+3)=0 by unfold hueDemand; omega]
    apply (Stationary.rays_jet ((aria_paid hW hp a).analytic_real ..) 0).2; omega

-- pre `Z` allowance a positive additional operator cost multiplying result,
-- uniformly chosen from pre quantities incl zero-momentum readout price.
variable (G)
def Golden (r : ℕ)(σ η C Z : ℝ)(L : Side) := ∀ {D} (F : Pot G (r+2)),Glow F σ D → ordered F → Dolce (hueDemand r) F →
     ∀ (U : Cross L (Loc G 1) (Loc G 1)),
      (∀ i : List Axis,i.length ≤ hueDemand r → (advanceC L U i).strip ((r+3:ℕ)*η) (C/(L.val:ℝ)^(1+i.length))) →
       Glow (flow F U) η ((D/Real.sqrt L.val)/Z)
lemma prosper (r : ℕ) {σ η C Z : ℝ}(h : 0<σ)(he : 0<η)(hc : 0 ≤ C)(hp : 0<Z) : ∃ N : ℕ, ∀ (L : Side),Odd L.val → N ≤ L.val → Golden G r σ η C Z L := by
  obtain ⟨v,W,hv,hq,hW,H⟩:= flow_soft (Loc G 1) (Loc G 1) (r+1) (hueDemand r) he h hc
  obtain ⟨N,hN⟩:= exists_nat_gt (max (((r+3:ℕ):ℝ)*η/v) ((W*Z)^2)); refine ⟨N,fun L ho hP D F Hg hF Hf U ht=>?_⟩
  have hx := hN.le.trans (show (N:ℝ) ≤ L.val by exact_mod_cast hP); have hl : 1 ≤ (L.val:ℝ):= by exact_mod_cast L.property
  have hC : 0 ≤ D:=Hg.nonneg; have hL : 0<Real.sqrt (L.val:ℝ):= by positivity
  apply glow_less (H L ho ((div_le_iff₀ hv).mp ((le_max_left ..).trans hx)) F U _ Hg hF Hf ht) le_rfl
  have hz : 5 ≤ r+1+1+hueDemand r := by unfold hueDemand; omega
  have hs : W*Z ≤ Real.sqrt L.val := (pow_le_pow_iff_left₀ (by positivity) hL.le (by decide: 2≠0)).1 (by rw [Real.sq_sqrt (by positivity)]; exact (le_max_right ..).trans hx)
  calc
    _ ≤ W*D*L.val^4/(L.val:ℝ)^5 := by gcongr
    _ ≤ _ := by
      apply (le_div_iff₀ hp).mpr
      apply (le_div_iff₀ hL).mpr
      have ht : W*Z*Real.sqrt (L.val:ℝ) ≤ (L.val:ℝ) := (mul_le_mul_of_nonneg_right hs hL.le).trans_eq <| by rw [← sq]; exact Real.sq_sqrt (by positivity)
      have h' := mul_le_mul_of_nonneg_left ht hC
      field_simp; -- exact?
      nlinarith [h']
end YM.RG08.Staffer
