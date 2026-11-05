import YM.RG08.Vale.Penny
import YM.Push.FREE_RESOLVENT.Torus
-- Data qualification BEFORE the block. Colors ordinary FRAME coordinates.
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option synthInstance.maxHeartbeats 120000
set_option maxHeartbeats 550000
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Exterior Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Place Shade Quire Source Source.Drops Labels
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} {m : Side} {d i j n r : ℕ}
variable {V W: Shale (Loc G 1) r}
abbrev Fare (G:Gauge) := Cover × Loc G 1
def heap (i : Fare G) : Edge Cover := (i.1,axisEquiv.symm i.2.1)
abbrev scent (i : G.ColorIndex) : G.Color→L[ℝ] ℝ := PiLp.proj 2 _ i

def screenR (G:Gauge) (d:ℕ) : LeafPath (Snap G d) (Loc G 1) :=
    fun i=> scent i.2.2 ∘ Film.lane (seat (heap i).1) (heap i).2
lemma pennydime (h : j<r)(X:Fin j→ Snap G d) : vault V (screenR G d) X=0 := sum_eq_zero fun i _=>by
  unfold penny; rw [grant_else (i.length_le.trans_lt h).ne,wallet_zero,mul_zero]
lemma starts (V:Fare G)(X:Snap G d) (H:Hol G) : screenR G d V X = scent V.2.2 (G.plog (G.mat (Place.pureQuest H X (heap V)))) := congr_arg (scent _) (Film.lane_truth ..)
lemma tariffR (G:Gauge) (d j : ℕ) : ∃ C:ℝ,0≤C ∧ ∀ i:Fare G, ‖iteratedFDeriv ℝ j (screenR G d i) 0‖ ≤ C*dime (d*j) i.1 := by
  obtain ⟨C,hc,hF⟩:= Film.mail_cap G d j
  let A := ∑ i:G.ColorIndex, ‖scent i‖
  have ha : 0 ≤ A:= by unfold A; positivity
  refine ⟨A*C,mul_nonneg ha hc,fun i=>?_⟩
  unfold screenR; rw [(scent i.2.2).iteratedFDeriv_comp_left (Film.lane_smooth ..) le_top]
  calc
   _ ≤ ‖scent i.2.2‖*‖iteratedFDeriv ℝ j (Film.lane (G:=G) (d:=d) (seat i.1) (heap i).2) 0‖:= ContinuousLinearMap.norm_compContinuousMultilinearMap_le ..
   _ ≤ A * (C*dime (d*j) i.1) := mul_le_mul (single_le_sum (f:=fun j=> ‖scent j‖) (fun k _=> norm_nonneg _) (mem_univ _)) (hF _ _) (norm_nonneg (iteratedFDeriv ℝ j (Film.lane (G:=G) (d:=d) (seat i.1) (heap i).2) 0)) ha
   _ = _ := (mul_assoc ..).symm
lemma fetchedR (G:Gauge) (d j r:ℕ):∃ C:ℝ,0≤C ∧ ∀ x:Fin j→Snap G d,∀ (V : Shale (Loc G 1) r) (A:ℝ), Ink (mint (d*j)) V A→ ‖vault V (screenR G d) x‖ ≤ C*A*∏ i,‖x i‖ := by
  apply Vale.receipt; intro n hn; obtain ⟨C,hc,H⟩:=tariffR G d n; exact ⟨C,hc,fun i=> (H _).trans (mul_le_mul_of_nonneg_left (dime_more (Nat.mul_le_mul_left d hn) _) hc)⟩

def studio (G:Gauge)(d:ℕ)(p:Side)(X:Snap G d) : Link G p := fun i=>screenR G d (lift i.1,i.2) X
lemma studio_open (p:Side) (i:Co p (Loc G 1)) : (fun X:Snap G d=> studio G d p X i)=screenR G d (lift i.1,i.2) := rfl
lemma begins (G:Gauge) (d:ℕ)(p:Side) : studio G d p 0=0 := funext fun i=> by simp [studio,screenR,Film.lane_root]
lemma begins_sm (G:Gauge)(d:ℕ)(p:Side): ContDiffAt ℝ ω (studio G d p) 0 := contDiffAt_pi.mpr fun _=> (scent _).contDiff.contDiffAt.comp _ (Film.lane_smooth ..)
lemma rotunda (G:Gauge)(d j:ℕ)(p:Side)(z)(x:Fin j→Snap G d) : iteratedFDeriv ℝ j (studio G d p) 0 x z=
    iteratedFDeriv ℝ j (screenR G d (lift z.1,z.2)) 0 x := by
  let P:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Co p (Loc G 1)=>ℝ) z
  have hp:(fun x=> studio G d p x z)=P ∘ studio G d p:=rfl
  rw [← studio_open p z,hp,P.iteratedFDeriv_comp_left (begins_sm ..) le_top]; rfl
def boards (i:ℕ) : Side := ⟨i+1,by omega⟩
lemma board_end : Tendsto (fun i=>(boards i).val) atTop atTop := tendsto_add_atTop_nat _
lemma rotor (G:Gauge) (d:ℕ) : Plenty (screenR G d) boards (fun i=>studio G d (boards i)) := by
  intro i x; refine ⟨fun u=> EventuallyEq.tendsto ?_,?_⟩
  · filter_upwards [Next.Free.eventually_unfold boards board_end u.1] with j hj
    rw [rotunda, (show lift (((wrap (boards j)) u.1,u.2) : Site (boards j) × Loc G 1).1=u.1 from hj)]
  obtain ⟨C,hC,hE⟩:=tariffR G d i
  let R:=∏ i, ‖x i‖; have hR: 0 ≤ R:= by unfold R; positivity
  refine ⟨d*i, C*R, mul_nonneg hC hR,fun u p=>?_⟩
  rw [rotunda]
  let w:Fare G:= (lift (wrap (boards p) u.1),u.2)
  calc
    _ ≤ ‖iteratedFDeriv ℝ i (screenR G d w) 0‖*R := (iteratedFDeriv ℝ i (screenR G d w) 0).le_opNorm x
    _ ≤ C * dime (d*i) w.1*R := mul_le_mul_of_nonneg_right (hE _) hR
    _ = C*R*dime (d*i) w.1:=mul_right_comm ..
    _ ≤ _ := mul_le_mul_of_nonneg_left (by unfold dime Carrier.liftCost w; gcongr; exact FreeResolvent.wrap_size (boards p) u.1) (mul_nonneg hC hR)
lemma radial_yes (hc : Tidy V)(hp: Polished V) (d j:ℕ):∃ M : Tensor.T (Snap G d) ℝ j, Tensor.Sym M ∧ ∀ x,M x=vault V (screenR G d) x := by
  obtain ⟨C,hC,H⟩:=hp (d*j) -- H? Ink expands conj
  apply piles board_end hc hp (rotor G d) (fun i=>begins_sm ..) (fun i=>begins ..) j
  intro x; exact (fetchedR G d j r).choose_spec.2 x V C ⟨hC,H⟩
def amount (V : Shale (Loc G 1) r) (d j:ℕ) : Tensor.T (Snap G d) ℝ j :=
    if h:Tidy V ∧ Polished V then (radial_yes h.1 h.2 d j).choose else 0
lemma coinSym (hc : Tidy V)(hp:Polished V)(d j:ℕ) : Tensor.Sym (amount V d j) := by rw [amount,dif_pos ⟨hc,hp⟩]; exact (radial_yes hc hp ..).choose_spec.1
lemma penny_amt (hc:Tidy V)(hp:Polished V)(x:Fin j→Snap G d): amount V d j x=vault V (screenR G d) x := by rw [amount,dif_pos ⟨hc,hp⟩]; exact (radial_yes hc hp d j).choose_spec.2 x
lemma movie (hc:Tidy V)(hp:Polished V)(x:Fin j→Snap G d) : Tendsto (fun i=> iteratedFDeriv ℝ j (rootSong V (boards i) 0 ∘ studio G d (boards i)) 0 x) atTop (𝓝 (amount V d j x)) := by
  rw [penny_amt hc hp]; exact plenish board_end hc hp (rotor G d) (fun i=>begins_sm ..) (fun i=>begins ..) x
@[simp] lemma zero_amt (G:Gauge) (r d j:ℕ): amount (0:Shale (Loc G 1) r) d j=0 := by
  ext1 x; rw [penny_amt (Tidy.zero ..) (polished_zero ℝ _ r),vault]; exact sum_eq_zero fun i _=>by simp [penny,grant_zero]
lemma amount_add (hc:Tidy V)(hp:Polished V)(he:Tidy W)(hf:Polished W) (d j:ℕ) : amount (V+W) d j=amount V d j+amount W d j := by
  ext1 x
  refine tendsto_nhds_unique_of_eventuallyEq (movie (hc.plus he) (polished_more hp hf) x) ((movie hc hp x).add (movie he hf x)) ?_
  refine Eventually.of_forall fun i=> ?_
  let L(U:Shale (Loc G 1) r):= rootSong U (boards i) 0 ∘ studio G d (boards i)
  have hl : L (V+W)= L V + L W := by unfold L rootSong; rw [st_plus hc.pens.of_norm he.pens.of_norm]; rfl
  change iteratedFDeriv ℝ j (L (V + W)) 0 x=_; rw [hl]
  have h (U:Shale (Loc G 1) r) : ContDiffAt ℝ j (L U) 0 := (((Tensor.diag_smooth ..).contDiffAt).comp _ (begins_sm ..)).of_le le_top
  rw [iteratedFDeriv_add_apply (h _) (h _)]; rfl
lemma amount_scale (hc:Tidy V)(hp:Polished V)(t:ℝ)(d j:ℕ) : amount (t•V) d j=t • amount V d j := by
  ext1 x
  refine tendsto_nhds_unique_of_eventuallyEq (movie (hc.scale _) (polished_scale hp _) x) (tendsto_const_nhds.smul (movie hc hp x)) ?_
  refine Eventually.of_forall fun i=>?_ ; let F (V:Shale (Loc G 1) r):= rootSong V (boards i) 0 ∘ studio G d (boards i)
  change iteratedFDeriv ℝ j (F (t•V)) 0 x=t • iteratedFDeriv ℝ j (F V) 0 x
  rw [show F (t•V)=t • F V from by unfold F rootSong; rw [st_scale _ hc.pens.of_norm]; rfl,iteratedFDeriv_const_smul_apply]; rfl
  exact (((Tensor.diag_smooth ..).contDiffAt).comp _ (begins_sm ..)).of_le le_top
lemma weights (G:Gauge)(d j r:ℕ): ∃ C:ℝ,0≤C ∧ ∀ (V : Shale (Loc G 1) r) (A:ℝ), Ink (mint (d*j)) V A → ‖amount V d j‖ ≤ C*A := by
  obtain ⟨C,hC,H⟩:= fetchedR G d j r
  refine ⟨C,hC,fun V A h=>?_⟩; have hx : 0≤C*A := mul_nonneg hC h.nonneg
  by_cases hh:Tidy V ∧ Polished V
  · exact ContinuousMultilinearMap.opNorm_le_bound hx fun x=> (by rw [penny_amt hh.1 hh.2]; exact H x _ _ h)
  rw [amount,dif_neg hh,show ‖(0:Tensor.T (Snap G d) ℝ j)‖=(0:ℝ) from @norm_zero (Tensor.T (Snap G d) ℝ j) _]; exact hx
end YM.RG08.Vale
