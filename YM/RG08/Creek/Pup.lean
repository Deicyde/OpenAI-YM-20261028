import YM.RG08.Creek.Cheeks
/-! # y-pol exponential strengthened certificate costs for primary columns. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall Scores Push.AbsoluteSums Work.F08 Door
open Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset RG Bloch Conductor Staffer Reflect UVExt.Paths Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Wings High Pill Taste Run Matrix PowerSeries
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {X:Chain} {G:Gauge}{E e r d τ D j t f i k m n :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}
variable {P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1 ≤ D}{T:Signals P Q E τ H Ω h hD}
variable {I J Y K:Type} [Fintype I][DecidableEq I]{u:Y→Windows}{a b:I→ℕ}{B: ℕ→ Side}{Z:ℕ→ℝ}
variable {p:J→ Dial u}
section stars
variable {A p':J→ ℝ}{U:J→Native (Letter F)}
private lemma cycle_a {q:K→ℝ} (hv:Audience q)(p: K→ℝ){F:K→ℝ}{U:K→Rooted (Voice D R) J r}{w:K→ℝ}(he:Tin q 1 U w)(h:Dig q p F): Tin q p (fun i=> F i • U i) w:=by
    obtain ⟨B,hB,hx⟩:=h.asset; obtain ⟨C,hC,ht⟩:=he.serves; simp only [Pi.one_apply,mul_one] at ht
    refine ⟨_,hB.times hC, fun i=> Ink.raise ((ht i).scale (F i)) (le_trans (mul_le_mul_of_nonneg_right (hx i) (hC.positive i)) (by simp [mul_comm,mul_left_comm]))⟩
lemma edge_e {A':K→Native (Letter F)}{B': K→ ReadsU F D R}{q p w:K→ℝ}(h:Audience q)(hv:∀ i≤e,∀ b r,Tin q 1 (fun j=>B' j b i r) w)(he:∀ i≤e,∀ b, Dig q p (fun j=> coeff i (A' j b))): Tin q p (fun i=>edgeBook (B' i) (A' i) e r) w:=by
   simp_rw [fun i=> accounting (B' i) (A' i) (e:=e) (r:=r)]; exact Tin.additions univ h (fun i _=> Tin.additions _ h (fun j hj=> cycle_a h p (hv _ (Nat.sub_le ..) _ _) (he j (mem_range_succ_iff.mp hj) i)))
lemma master_income (h:Tights T S ν D' u)(hp:e≤E)(hZ:0≤A)(hx:∀ j≤e,∀ a:Letter F,Dig (fun i=> Dial.fee X (p i)) A (fun i=> coeff j (U i a))) : Tin (glass X) (fun i: High p 0=> A i.z) (fun i:High p 0=> masters X ν D' T (p i.z).N (p i.z).K i.i (U i.z) e r) (fun i=> ώ T i.i):=by
   let y: High p 0→ℝ:= glass X; have hz:=glint X p 0; let Δ:= High.defect (b:=p) (n:=0) X
   let F':=Ye (u:=u) X ν D' T; let C':= fun i:High p 0=> U i.z
   have hu (j)(hj:j≤e)(b:Letter F): Tonic y (fun i=> A i.z) Δ (fun i=> coeff j (C' i b)) (fun i=> coeff j (C' i b)):= by
      obtain ⟨B,hB,H⟩:= (hx j hj b).asset; have hh : Dig y (fun i=>A i.z) (fun i=>coeff j (C' i b)):= ⟨_, (here_bill X).sway hz (hB.transfer Plot.High.z),fun i=> H i.z⟩
      exact ⟨hh,hh,by rw [sub_self]; exact Dig.zero⟩
   let A' i:=waitP (b:=p) i; let Z (i:High p 0) (j:Bool):= (trump T ν D' ((ite j (p i.z).N (p i.z).M):ℕ) (p i.z).K (p i.z).K (i.i-i.K))*ᵥ C' i -- annotate bool
   have hC: Weighed y (fun i=> (A' i).y X):= by unfold A'; simp_rw [High.spend]; simpa only [pow_one] using Weighed.power _ (glint X p 0) 1
   have ht i (hi:i≤e) a:= trump_d h A' hC (fun i=> le_of_eq (High.joust X i)) (fun i=>hZ i.z) (glint X p 0) (fun j hj a=> hu j (le_trans hj hi) a) (hi.trans hp) a
   unfold masters; apply edge_e (B':=fun j=>F' j.appr) hz (fun i hi b r=> Tin.move appr (cashIn h (hi.trans hp) b r))
   intro i hi a; let w i:= A' i |>.next; have hx : Weighed y (fun i=>(w i).measure X):= by simpa only [pow_one] using! Weighed.power y (glint X p 0) 1
   have hg(j)(hj:j ≤ i)(v:Letter F): Tonic y (fun i=> A i.z) Δ (fun i=> coeff j (Z i true v)) (fun i=> coeff j (Z i false v)):= ht _ (hj.trans hi) _
   exact (forward_d h hx (fun i=> le_of_eq (High.joust X i)) (fun i=>hZ _) hz hg (hi.trans hp) a).one
end stars
section familiesCoupon
variable {F: ∀ i:I, Labels.Frame G (a i)}{A: ∀ i,SectionData (F i)}{hZ:∀ i:I,a i+1≤D} {B':∀ i, Signals P Q E τ H (A i) h (hZ i)}
lemma money_stacks (Z: ℕ→ℝ)(hp:∀ i:I,Tights (B' i) S ν D' u)(q:I→J→ℝ)(hx:∀ i,0≤ q i)(hQ:∀ i j,Z i≤ (B' j).wi i) (K : ∀ i:I,J→Native (Letter (F i)))(hV:∀ i,∀ j ≤ E,∀ a:Letter (F i),Dig (tribute X p) (q i) (fun x=> coeff j ((K i x) a))):
   Attract ν D' X p (deckR X ν D' B' K p) a a ∧ Bureau Z E X (deckR X ν D' B' K p) p q:= by
   refine ⟨⟨fun s i=> mastery (hp i) s _|>.1,fun s i=> mast_step (hp i) s _⟩,fun k hk j r=>?_⟩
   exact (master_income (hp j) hk (hx j) (fun i hi a=> hV j i (hi.trans hk) a)).soften (fun i=> hQ _ _)
lemma stack_gate (T:Signals P Q E τ H Ω h hD)(B:∀ i:I, Signals P Q E τ H (A i) h (hZ i)): ∃ w:ℕ→ℝ,(∀ i,0<w i)∧ (∀ i,w i ≤ secretT T I i)∧ (∀ i (j:I), w i ≤ (B j).wi i):= by
   let v (i:ℕ):ℝ:= (secretT T I i)⁻¹+ ∑ j:I, ((B j).wi i)⁻¹; have hv i:0<v i:= add_pos_of_pos_of_nonneg (inv_pos.mpr (secret_t ..)) (sum_nonneg fun j _=> inv_nonneg.mpr ((B j).pos i).le)
   refine ⟨fun i=>(v i)⁻¹,fun i=>inv_pos.mpr (hv i),fun i=>(inv_anti₀ (inv_pos.mpr (secret_t T I i)) (show _ ≤ v i from le_add_of_nonneg_right (sum_nonneg fun j _=> inv_nonneg.mpr ((B j).pos i).le))).trans_eq (inv_inv _),fun i j=>?_⟩
   have hp : ((B j).wi i)⁻¹ ≤ v i:= (single_le_sum (s:=univ) (f:=fun j=> ((B j).wi i)⁻¹) (fun j _=>inv_nonneg.mpr ((B j).pos _).le) (mem_univ j)).trans (le_add_of_nonneg_left (inv_nonneg.mpr (secret_t ..|>.le)))
   exact (inv_anti₀ (inv_pos.mpr ((B j).pos i)) hp).trans_eq (inv_inv _)
end familiesCoupon
end YM.RG08.Creek
