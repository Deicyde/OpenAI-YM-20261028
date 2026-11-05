import YM.RG08.Crossing.Cue
/-! # Bill strict event for one partner or two uniformly
-/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Wings
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open scoped BigOperators Topology Real Classical
variable {X : Chain} {G : Gauge} {K : KPrices X.kernel} {g : KGate K} {P : Lending G X.kernel} {E : ℕ} {S : Prism G X.kernel g P E} {ν : G.ColorIndex} {D : ChartRatio G}
variable {I : Type} {u : I→Windows} {r s e q : ℕ} {δ : Wings u 1→ℝ}

-- either identity or wingR
structure Partner (S : Prism G X.kernel g P E) (δ : Wings u 1→ℝ) (N' : Wings u 1→ℕ) : Prop where
  geC i : i.N ≤ N' i
  pos : 0 ≤ δ
  a₁ : RowBoth (menu X) δ (fun i=> Chain.curve G X i.N i.i) (fun i=> Chain.curve G X (N' i) i.i) (fun i=> ticketW P (X.J i.i))
  a₂ : RowBoth (menu X) δ (fun i=> Chain.predict G X i.N i.i) (fun i=> Chain.predict G X (N' i) i.i) (fun i=> ticketW P (X.J i.i))
  a₃ : Both (menu X) δ (orbit X) (fun i=> Chain.column G X (N' i) i.i) (fun i=>Tier S i.i)
lemma single (h : Circuit S ν D u)(hs : X.Wake G) : Partner S (u:=u) 1 N := by
  have hx:= gear_both h hs; constructor
  · exact fun i=> le_rfl
  · exact zero_le_one
  · refine ⟨hx.1.1,hx.1.1,?_⟩; rw [sub_self]; exact ⟨0,Weighed.zero,fun i=> by change (0:Row _ _).strip _ (0*1); rw [zero_mul]; exact fun _ _=> by simp [Width,SumBudget]⟩
  · refine ⟨hx.2.1,hx.2.1,?_⟩; rw [sub_self]; exact ⟨0,Weighed.zero,fun i=> by change (0:Row _ _).strip _ (0*1); rw [zero_mul]; exact fun _ _=> by simp [Width,SumBudget]⟩
  exact Both.self ((q_right h).fresh.mold low)
lemma doubleL (h : Circuit S ν D u)(hs : X.Wake G) : Partner S (u:=u) (chop X (1/4)) M := by
  refine ⟨side,fun i=> (gain_pos ..).le,(gear_both h hs).1, (gear_both h hs).2,?_⟩
  have hw:= q_right h; exact ⟨hw.fresh.mold low,hw.again.mold low,hw.moves.mold low⟩
variable {A : Wings u 1→ℕ} (hx : Partner S δ A)

def Partner.there (t : Wings u 1) : Wings u 1 := {t with N:=A t,M:=A t,side:=le_rfl,cut:=t.cut.trans (hx.geC t)}
variable {hx}
lemma strictBill (h : Circuit S ν D u) {e r}(he : e ≤ E)(hp : r ≤ e+2)(hW : X.Wake G) (hv : LocalRatio D)
    (hx : Partner S δ A) (hF : ∀ j p, RootStep 1 e r j p → Both (menu X) δ (fun i=> moon X ν D i.up j p) (fun i=> moon X ν D (hx.there i).up j p) (fun i=>Tier S (i.i+1))) :
    Both (menu X) δ (dark X ν D e r) (fun i=> dark X ν D e r (hx.there i)) (fun i=>Tier S i.i) :=
   harvest_g (F:=fun i=> moon X ν D (up i)) (H:=fun i=> moon X ν D (hx.there i).up) (h.M.move toLaunch) hx.pos (fun _=> ticket_pos ..) hx.a₁ hx.a₂ (show _ ≤ _ from fun i=> S.strict_event _) he hp (fun _=> S.positive _) (fun i=> (S.positive _).le) (hire h) (fun _=> (rallies hW hv _).totes.1) (fun _=> (rallies hW hv _).totes.1) hF
lemma adaptBill (h : Circuit S ν D u) (hx : Partner S δ A) {e}(he:e=r+2*q) (hp : 0 < r+2*q) (hF : ∀ j p, RootStep 1 e (r+2) j p → Both (menu X) δ (fun i=> lunar X ν D i j p) (fun i=> lunar X ν D (hx.there i) j p) (fun i=>Tier S i.i)) : Both (menu X) δ (fun i=> morph X i ν D r q) (fun i=> morph X (hx.there i) ν D r q) (fun i=>Tier S i.i) := by
  subst e
  cases r with
  | zero=>
    cases q with
    | zero=>omega
    | succ j=> simp only [morph,Nat.add_sub_cancel]; exact duetCharge ν (sh X) (fun i=> S.positive _) (h.cup.transfer toLaunch) _ (fun i he hp=> hF _ _ ⟨⟨by omega,i,by omega⟩, Or.inl (by omega)⟩) hx.a₃
  | succ i=> exact titanCharge ν (sh X) (fun _=> S.positive _) (h.cup.transfer toLaunch) _ _ (fun j he hp=> hF (2*j) 2 ⟨⟨by omega,j,Nat.add_comm ..⟩, Or.inl (by omega)⟩) (fun j he=> hF (i+1+2*j) (i+3) ⟨⟨by omega,j,by omega⟩, Or.inl (by omega)⟩)
lemma duskBill (h : Circuit S ν D u)(hW : X.Wake G)(hv : LocalRatio D) (hx : Partner S δ A){e}(he : e=r+2*q) (hp : 0<e)(hk : e≤ E) (hF : ∀ j p, RootStep 1 e (r+2) j p → Both (menu X) δ (fun i=> moon X ν D i.up j p) (fun i=>moon X ν D (hx.there i).up j p) (fun i=>Tier S (i.i+1)) ∧ Both (menu X) δ (fun i=> lunar X ν D i j p) (fun i=>lunar X ν D (hx.there i) j p) (fun i=>Tier S i.i)) : Both (menu X) δ (fun i=> dusk X i ν D r q) (fun i=> dusk X (hx.there i) ν D r q) (fun i=>Tier S i.i) := by
  subst e
  exact (penny_both ν (sh X) (fun _ => S.positive _) (h.cup.transfer toLaunch) hx.a₃ (strictBill h hk (by omega) hW hv hx (fun j p hj=>(hF j p hj).1))).add (adaptBill h hx rfl hp (fun j p hj=> (hF j p hj).2)) (sh X)
lemma featBill (h : Circuit S ν D u)(hx : Partner S δ A) (he:r ≤ E+2) {F H : Wings u 1→Pot G r}(hv : Both (menu X) δ F H (fun i=>Tier S (i.i+1))) : Both (menu X) δ
    (fun i=>feather (F i) (Chain.predict G X i.N i.i)) (fun i=>feather (H i) (Chain.predict G X (A i) i.i)) (fun i=> Tier S i.i) := by
  let ψ t := ticketW P (X.J (t:Wings u 1).i)
  have hZ t: 0 ≤ ψ t:= (ticket_pos ..).le
  have ht := gem_accrue (L:=fun i=> X.S.block (i:Wings u 1).i) r (h.M.crop.transfer toLaunch) (sh X) (show 0≤ ψ from hZ) (fun _=> min_le_right ..) (fun _=> (S.positive _).le) (fun i=> (smul_le_smul_of_nonneg_right (show r+1 ≤ E+3 by omega) (hZ i)).trans (hire h i)) hv
  exact remit (w:=fun i:Wings u 1=> Tier S i.i) (fun _=>S.positive _) (sh X) hx.pos (ht.soften (fun _=> ticketV S he _)) (scanned_contract hx.a₂ (fun i=> ticketV S he _) (sh X) hx.pos) (Weighed.constant _ (Nat.cast_nonneg (Fintype.card (Loc G 1))))
lemma tiltBill (h : Circuit S ν D u)(hx : Partner S δ A) (he:r ≤ E) {F H : Wings u 1→Pot G (r+2)}(hv : Both (menu X) δ F H (fun i=>Tier S (i.i+1))) : Both (menu X) δ (fun i=> tilted X i ν (F i)) (fun i=> tilted X (hx.there i) ν (H i)) (fun i=>Tier S i.i) := by
    apply penny_both ν (sh X) (fun _=>S.positive _) (h.cup.transfer toLaunch) hx.a₃ (featBill h hx (by omega) hv)
lemma rawBill (h : Circuit S ν D u)(hx : Partner S δ A)(hW : X.Wake G)(hp : LocalRatio D)(he:e ≤ E)(hr:r ≤ e+2) (hv : Both (menu X) δ (fun i=> moon X ν D i.up e r) (fun i=> moon X ν D (hx.there i).up e r) (fun i=>Tier S (i.i+1)))
    (hF : ∀ j p, RootStep 1 e r j p → Both (menu X) δ (fun i=> moon X ν D i.up j p) (fun i=> moon X ν D (hx.there i).up j p) (fun i=>Tier S (i.i+1))) :
    Both (menu X) δ (fun i=> lunar X ν D i e r) (fun i=> lunar X ν D (hx.there i) e r) (fun i=>Tier S i.i) := by
  simp_rw [obverse hW hp]; exact (featBill h hx (by omega) hv).add (strictBill h he hr hW hp hx hF) (sh X)
end YM.RG08.Wings
