import YM.RG08.Door.Receive
/-!
# Path witness bills post in still-uniform width. Single call. No convergence of turn
choice required.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels
open scoped BigOperators Topology Real Classical
section
variable {E α β : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E][Fintype β]{r : ℕ}{w σ C A:ℝ}{L:Side}{P:Quire.Rooted E α r}{Q:Cross L α β}
lemma whirl (i: Site L)(hQ:Q.strip w A)(hv:0≤w)(hp:Quire.Lit P σ C)(h:w ≤ L.val * σ)(hA:0≤A) : Quire.Lit (belly i Q P) w (((Real.exp (4*w)*(Fintype.card β)*A)^r)*C):= by
  unfold belly; rw [Quire.Lit, show (ling w : Beads β r→ℝ)=brocade (plyH w) from funext fun _=> bro_lit ..]
  let p := Real.exp (4*w)*(Fintype.card β)*A; have hh :0≤p:= by unfold p; positivity
  apply Ink.raise (revolves (P:=fun _=> node i Q) (show Quire.Ink (brocade (plyH σ)) P C from (by rw [show brocade (plyH σ)=(ling σ:Beads α r→ℝ) from funext fun i=>(bro_lit ..).symm]; exact hp)) (p:=fun _=>p) (fun _=>hh) (fun _ j=> Ink.raise (nodeExp hQ hv le_rfl i j) ?_) (plyH_one hv))
  · simp only [p,prod_const,card_univ,Fintype.card_fin,le_refl]
  let a:ℝ:= (L.val:ℝ)⁻¹
  have hu : w*a ≤ σ := by unfold a; rw [← div_eq_mul_inv, div_le_iff₀ (by positivity : 0<(L.val:ℝ))]; simpa only [mul_comm σ] using h
  have hz : Real.exp (w*(4+a*size j.1))≤ Real.exp (4*w)* plyH σ j:= by unfold plyH; rw [← Real.exp_add]; apply Real.exp_monotone; rw [mul_add,mul_comm w,← mul_assoc]; linarith only [mul_le_mul_of_nonneg_right hu (show 0≤((size j.1:ℕ):ℝ) by positivity)]
  refine (mul_le_mul_of_nonneg_right hz (by positivity)).trans_eq ?_; unfold p; ring
end
section
variable {X:Chain}{G:Gauge}{E e r d τ D j t i k m :ℕ}{R C A:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
open Wings
variable {I:Type}{u:I→Windows}
local notation "L" => (X.S.block i)
variable {l : Launch u} {V:EnvelopeU D R G j}
lemma amber (Z:Cross (X.S.block l.i) (Candles G) (Loc G 1))(b:Site (X.S.block l.i))(hE:Enabled T u)(hz:Z.strip (ώ T l.i) C)(hx:0≤C)(hu:r ≤ τ+E)
    (hN: Quire.Lit V (ώ T (l.i+1)) A):
    let a:=ώ T (l.i+1) / (τ+E+1:ℕ)
    Quire.Lit (rue b Z V r) (ώ T l.i) ((Real.exp (4*ώ T l.i)*Fintype.card (Loc G 1)*C)^r * ((Real.exp (r*a)* silkSale G j r)*A)) := by
  intro a; let B k:= readdress (V k) b
  have h : Quire.Lit B (ώ T (l.i+1)) A := budget_mono hN (fun i=>mul_nonneg (ling_pos _ _).le (norm_nonneg _)) (fun k=> mul_le_mul_of_nonneg_left (Shade.read_scores (X.S.block_odd _) h _ (V k)).1 (ling_pos _ _).le)
  have he:0<a:= div_pos (T.pos _) (by positivity)
  have hv: Quire.Lit (crock B r) a ((Real.exp (r*a)*silkSale G j r)*A):= crock_bills h he.le (le_trans (mul_le_mul_of_nonneg_right (show (r:ℝ)≤(τ+E+1:ℕ) by exact_mod_cast (Nat.le_trans hu (Nat.le_succ _))) he.le) (le_of_eq ?_))
  · exact whirl b hz (T.pos _|>.le) hv ((tick_t T _).1.trans (hE.stepV l)) hx
  unfold a; rw [mul_div_cancel₀ _ (by positivity)]
lemma ameth (Z:∀ i:Wings u 1, Cross (X.S.block i.i) (Candles G) (Loc G 1))(hZ:SafeRow (menu X) 1 Z (fun i=> ώ T i.i)) (hE: Enabled T u)(hu:r ≤ τ+E)(V:Wings u 1→EnvelopeU D R G j)
    {δ: Wings u 1→ℝ}(hp:Tin (menu X) δ V (fun i=> ώ T (i.i+1))) (hy:Weighed (menu X (u:=u) (r:=1)) (fun i=> ((X.S.block i.i).val:ℝ))):
    Tin (menu X) δ (fun i=> ((↑(X.S.block i.i).val:ℝ)^d *((Fintype.card (Site (X.S.block i.i)):ℝ))⁻¹) • ∑ b:Site (X.S.block i.i),rue b (Z i) (V i) r) (fun i=>ώ T i.i) := by
  obtain ⟨C,hC,H⟩:= hZ; obtain ⟨D,hD,Ht⟩:=hp.serves
  let a i:= ώ T ((i:Wings u 1).i+1) / (τ+E+1:ℕ)
  let X' i:= Real.exp (4*ώ T (i:Wings u 1).i)
  let Y i:= Real.exp ((r:ℝ)*a i)
  have h i : ώ T i ≤ 1:= by
    have he:=tick_t T (X.J i); exact (he.1.trans he.2).trans (min_le_right ..)
  have he : Weighed (menu X) X' := (Weighed.constant (menu X) (Real.exp_pos 4|>.le)).mono (fun i=> (Real.exp_pos _).le) (fun i=>Real.exp_monotone (mul_le_of_le_one_right (by norm_num) (h _)))
  have hh : Weighed (menu X) Y:= (Weighed.constant (menu X) (Real.exp_pos r|>.le)).mono (fun _=>(Real.exp_pos _).le) (fun i=>Real.exp_monotone (mul_le_of_le_one_right (Nat.cast_nonneg r) ((div_le_self (T.pos _).le (by norm_cast; omega)).trans (h _))))
  have hb i (b) := amber (l:=(i:Wings u 1).toLaunch) (Z i) b hE (C:=C i) (by simpa using H i) (hC.positive i) hu (Ht i)
  refine ⟨_, (hy.powers d).times ((((he.times (Weighed.constant (menu X) (Nat.cast_nonneg (Fintype.card (Loc G 1))))).times hC).powers r).times ((hh.times (Weighed.constant _ (silkSale_pos G j r))).times hD)), fun i=> Ink.raise (Ink.scale (Ink.additions (f:=fun b:Site (X.S.block i.i)=>rue b (Z i) (V i) r) (fun b _=>hb i b) (fun b=>(ling_pos _ _).le)) _) (le_of_eq ?_)⟩ -- let dims
  simp only [sum_const,card_univ,nsmul_eq_mul,Pi.mul_apply]; let Q:= Fintype.card (Site (X.S.block i.i)); have he:0<Q:=Fintype.card_pos
  rw [Real.norm_of_nonneg (by positivity)]
  unfold X' Y a; field_simp
lemma tulip (hE:Enabled T u)(Z:∀ i:Wings u 1, Cross (X.S.block i.i) (Candles G) (Loc G 1))(hz: SafeRow (menu X) 1 Z (fun i=>ώ T i.i)) (V:Wings u 1→BoardU D R G){δ:Wings u 1→ℝ}(he:r≤ τ+E)(hx:r≤m+e)
    (hp:∀ i< e,∀ j,Tin (menu X) δ (fun b=> V b i j) (fun i=>ώ T (i.i+1)))(hy:Weighed (menu X (u:=u) (r:=1)) (fun i=> ((X.S.block i.i).val:ℝ))) :
    Tin (menu X) δ (fun i=>curse m (m+e-r) r d (V i) (Z i)) (fun i=>ώ T i.i) := by
  let A j i:= moreU m (m+e-r) (V i) j
  have h j (hj:j<r) : Tin (menu X) δ (A j) (fun i=>ώ T (i.i+1)):= by
    unfold A moreU; split; next h=> apply hp; omega
    exact Tin.zero
  let W j i:= ((↑(X.S.block (i:Wings u 1).i).val:ℝ)^d *((Fintype.card (Site (X.S.block i.i)):ℝ))⁻¹) • ∑ b:Site (X.S.block i.i),rue b (Z i) (A j i) r
  rw [show (fun i=>curse m (m+e-r) r d (V i) (Z i))=(fun i=> ∑ j∈ range r,W j i) from funext fun i=> by unfold curse; rw [sum_comm, Finset.smul_sum]]
  exact Tin.additions _ (sh X) fun j hj=> ameth Z hz hE he (A j) (h j (mem_range.mp hj)) hy

end
end YM.RG08.Door
