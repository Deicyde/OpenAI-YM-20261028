import YM.RG08.Action.Gallant

/-! # Pre-block Ward monetary demands, history independent. All windows. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Filter MeasureTheory
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free
open PertExtension.Series.Tested PertExtension.Series.Radial Matrix Conductor Bloch UVExt.Paths Work.F08 Push.AbsoluteSums Staffer
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {k : KernelChoices} {X : Chain} {G : Gauge} {K : KPrices k} {g : KGate K} (P : Lending G k) (E : ℕ)

def qCap (G : Gauge)(C : ℝ):= ‖(1/2:ℝ)‖ * ((Fintype.card (Loc G 1):ℝ)*((Fintype.card (Loc G 1):ℝ)*C))
lemma qCap_pos (G : Gauge){C : ℝ}(hp : 0≤C) : 0≤ qCap G C := by unfold qCap; positivity

def share (G : Gauge)(v C : ℝ) := 1+probeFee G v*qCap G C
lemma share_one (G : Gauge)(v : ℝ){C}(h:0≤C) : 1 ≤ share G v C := le_add_of_nonneg_right (mul_nonneg (probe_fee ..) (qCap_pos G h))

-- τ auxiliary intermediate width, η state transition. `Golden` order=0..E.
def ticketW (P : Lending G k) (j : ℕ) := min (P.w j) (1:ℝ)
lemma ticket_pos (j) : 0<ticketW P j := lt_min (P.wpos _) zero_lt_one
structure Prism (G : Gauge)(k : KernelChoices) {K : KPrices k} (g : KGate K)(P : Lending G k)(E : ℕ) where
  η : ℕ→ℝ
  height : ℕ→ℕ
  hired i : ∀ j:ℕ,i=j ∨ i=j+1 → ∀ (L : Side), height i ≤ L.val → Odd L.val →
      P.w j ≤ L.val*g.w i ∧
      (E+3:ℕ) • ticketW P j ≤ L.val*(η i / ((E+3:ℕ):ℝ)) ∧
      ∀ r:ℕ,r ≤ E → Golden G r (η i) (η j) (K.bill j) (share G (η j) (K.bill j)) L
  positive i : 0 < η i
  sufficient i : η i ≤ g.w i
  shade i : (E+3:ℕ) • η i ≤ ticketW P i
  shine i : (E+3:ℕ) • η i ≤ K.b i
  strict_event i : ticketReach E • η i ≤ ticketW P i
  kprice i : g.minimum i ≤ height i
-- future may prescribe GIVEN η w/conditions. Quant fine integer table independent lengths
private lemma small_coordinate (P : Lending G k)(g : KGate K) (E : ℕ)(i : ℕ) : ∃ v : ℝ,0<v ∧ v≤g.w i ∧ (E+3:ℕ) • v≤ ticketW P i ∧ (E+3:ℕ) • v≤K.b i ∧ ticketReach E • v ≤ ticketW P i := by
  let n := max (E+3) (ticketReach E); have he:(E+3:ℕ) ≤ n:= le_max_left ..
  have hN : (1:ℝ) ≤ (n:ℝ):= by exact_mod_cast (by omega:1≤n)
  let s := min (K.b i) (min (ticketW P i) (g.w i)); have hp:0<s:=lt_min (K.positive i) (lt_min (ticket_pos ..) (g.pos _))
  let v := s/n; have hv: 0<v:=div_pos hp (by positivity : 0<(n:ℝ))
  have h x (hx : x≤ n): x • v ≤ s := by apply (smul_le_smul_of_nonneg_right hx hv.le).trans_eq; unfold v; rw [nsmul_eq_mul,mul_div_cancel₀ s (by positivity)]
  have hh:s ≤ ticketW P i:=(min_le_right ..).trans (min_le_left ..); refine ⟨v,hv,(div_le_self hp.le hN).trans ((min_le_right ..).trans (min_le_right ..)), (h _ he).trans hh,(h _ he).trans (min_le_left ..), (h _ (le_max_right ..)).trans hh⟩
lemma scheduled_prism (G : Gauge) (g : KGate K) (P : Lending G k) (E : ℕ) : Nonempty (Prism G k g P E) := by
  choose v hp hf hh hs he using small_coordinate P g E
  choose A hA using fun r j i=> prosper G r (hp i) (hp j) (K.solvent j) (lt_of_lt_of_le zero_lt_one (share_one G (v j) (K.solvent j)))
  choose L hL using fun j i=> exists_nat_gt (max (P.w j/g.w i) (((E+3:ℕ) • ticketW P j)/(v i/((E+3:ℕ):ℝ))))
  let M j i := max (L j i) ((range (E+1)).sup (fun r=> A r j i))
  let V i := max (g.minimum i) (max (M i i) (M (i-1) i)); refine ⟨⟨v,V,?_,hp,hf,hh,hs,he,fun i=> le_max_left ..⟩⟩
  intro i j hv l hl ho
  have h : M j i ≤ l.val := le_trans (le_trans (b:=max (M i i) (M (i-1) i)) ?_ (le_max_right ..)) hl
  · have hu := hL j i; have hℓ := hu.le.trans (show (↑(L j i) : ℝ)≤ ↑l.val by exact_mod_cast ((le_max_left ..).trans h: L j i≤l.val))
    refine ⟨(div_le_iff₀ (g.pos i)).1 ((le_max_left ..).trans hℓ), (div_le_iff₀ (div_pos (hp _) (by positivity))).1 ((le_max_right ..).trans hℓ),fun r hr=> hA r j i l ho ?_⟩
    exact ((le_sup (s:=range (E+1)) (f:=fun r=> A r j i) (b:=r) (mem_range.mpr (Nat.lt_succ_of_le hr))).trans (le_max_right ..)).trans h
  rcases hv with h|h <;> subst i; · exact le_max_left ..
  rw [Nat.add_sub_cancel]; exact le_max_right ..
section
variable {K : KPrices X.kernel} {g : KGate K} {P : Lending G X.kernel} {E : ℕ} (S : Prism G X.kernel g P E) (ℓ m : ℕ)
structure OnBoard : Prop where
   lit : 5 ≤ X.J (ℓ+1) -- use monotone
   step (i : ℕ) : ℓ ≤ i → S.height (X.J (i+1)) ≤ (X.S.block i).val
lemma OnBoard.books {ℓ}(h : OnBoard S ℓ) : KAllowed g ℓ := by
  refine ⟨fun i hi=> (S.kprice _).trans (h.step _ hi), fun i hi=> h.lit.trans ((monotone_nat_of_le_succ X.mono) (by omega))⟩
-- E fixed
lemma OnBoard.shift {m ℓ} (hx : OnBoard S ℓ)(h : ℓ ≤ m) :
    let L:=X.S.block m
    let i:=X.J (m+1); let j:=X.J m; let v:=S.η
    P.w j ≤ L.val*g.w i ∧
      ((E+3:ℕ) • ticketW P j) ≤ L.val*(v i / ((E+3:ℕ):ℝ)) ∧
      ∀ r:ℕ,r ≤ E → Golden G r (v i) (v j) (K.bill j) (share G (v j) (K.bill j)) L :=
    S.hired _ _ (by have he:=X.mono m; have hp:=X.slow m; omega) _ (hx.step m h) (X.S.block_odd _)
lemma OnBoard.clear {ℓ} (hx : OnBoard S ℓ)(h : X.Wake G) : Clear K g P ℓ := ⟨hx.books S, fun _ hi=>(OnBoard.shift S hx hi).1,h⟩
lemma Q_loans (N i) : Glow (X.column G N i) (S.η (X.J i)) (qCap G (K.bill (X.J i))) := by
  have hv : (X.K₀ N i).strip _ _ := strip_mono (k_strip X K N i) ((S.sufficient _).trans (g.small _)) le_rfl
  exact (quad_matches G (X.K₀ N i) hv (S.positive _).le (fun p=> by rw [X.sym_acts]; exact k_symmetric (X.metric_sym ..))).1
lemma Q_change {i N N' : ℕ}{η B : ℝ} (h : 0 < η) (hp : (X.K₀ N i-X.K₀ N' i).strip η B) :
    Glow (X.column G N i-X.column G N' i) η (qCap G B) := by
  rw [show X.column G N i-X.column G N' i= quad G (X.K₀ N i-X.K₀ N' i) from (quad_sub G (X.k_whole ..) (X.k_whole ..)).symm]
  refine (quad_matches G _ hp h.le (fun c=>?_)).1
  change ((minusRows (X.K₀ N i) (X.K₀ N' i)).acts c)ᵀ=(minusRows (X.K₀ N i) (X.K₀ N' i)).acts c
  rw [(X.k_whole N i).less (X.k_whole N' i), Matrix.transpose_sub,X.sym_acts,X.sym_acts,k_symmetric (X.metric_sym ..),k_symmetric (X.metric_sym ..)]
lemma A_loans (N m) (s) (h : List.length s≤ X.J (m+1)-2){r:ℕ}(hr : r≤E+3) :
    (advanceC _ (painted G (X.A₀ N m)) s).strip (r • S.η (X.J m)) (K.bill (X.J m)/((X.S.block m).val:ℝ)^(1+s.length)) := by
  rw [paint_diffs]; exact strip_mono (paint_budget (az_strip X K N m s h)) ((smul_le_smul_of_nonneg_right hr (S.positive _).le).trans (S.shine _)) le_rfl
lemma pre_gain {ℓ} (hx : OnBoard S ℓ){N m : ℕ} (hi : ℓ≤m) {r:ℕ}(hr:r≤E) {V : Pot G (r+2)} {D : ℝ} (hV : Glow V (S.η (X.J (m+1))) D)(hT : ordered V)(hq : Dolce (hueDemand r) V) :
    Glow (feather V (painted G (X.A₀ N m))) (S.η (X.J m)) ((D/Real.sqrt (X.S.block m).val)/share G (S.η (X.J m)) (K.bill (X.J m))) := by
  have H (s) (hs : List.length s≤hueDemand r) := A_loans S N m s (by
    have hh := (OnBoard.books S hx).order m hi; unfold hueDemand at *; omega) (r:=r+3) (by omega)
  have ht := X.az_whole N m; obtain ⟨v,x,hP,h⟩:=ht
  rw [feather_step (hV.summable (ling_one (S.positive _).le)) (show Whole (painted G (X.A₀ N m)) from ⟨_,_,hP,paint_budget h⟩)]
  exact (OnBoard.shift S hx hi).2.2 r hr V hV hT hq _ (by simpa only [← nsmul_eq_mul] using H)
end
end YM.RG08
