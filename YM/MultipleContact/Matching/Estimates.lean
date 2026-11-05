import YM.MultipleContact.Matching.Arena
import YM.MultipleContact.Matching.Economist
import YM.MergeProof.West.Ozone

/-! Euclidean estimates about the anchor with external cell positions kept compact and safe. -/

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MultipleContact.Local
open Filter Function MeasureTheory Analysis Extraction Table Ward MergeProof Acme Ribbons Around Cells Wilson Lattice Climb Set
open Matching
open scoped Topology BigOperators Classical ContDiff
open YM.Next.UVStress
variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Extraction.Order}{W:DiffPlan S} {t d D J:ℕ} (hG:G.Simple)
variable {ι:Type*}[Fintype ι]{n:ι→ℕ}
variable (K:Set ((i:ι)→Points (n i)))(hK:IsCompact K)(hsafe:∀x∈K,∀i, Points.cons 0 (x i) ∈ conf (n i+1))
variable (hT:Acme.Aroma C)(hh:Matching C)
local notation "R'"=>fun (m:ℕ)=> fuga C.path.levels (m+1)
local notation "Yb"=>fun (m:ℕ)=> topZone C.path.levels (C.S.block m) (m+1)
-- when weighted sum of outputs cancels for every field
variable (q:∀i:ι,Fin (n i)→ C.book.Token)
def silent (S:Table C.book)(D:ℕ)(z:∀i,Points (n i))(c:ι→ℂ):Prop:=∀ v:S.Field D,(∑ i:ι,c i * once (q i) ⟨D,v⟩ (z i))=0

def predicate (q:∀i:ι,Fin (n i)→ C.book.Token)(V B:S.Tag)(P:((i:ι)→Points (n i))→(ι→ℂ)→Prop)(w:ℝ):Prop:=
    ∃ r:ℝ,0<r∧∀z∈K,∀c:ι→ℂ,(∑ i:ι,‖c i‖)≤1→ P z c → ∀y:E4,0<‖y‖→‖y‖ < r → ‖combo q V B c z y‖≤‖y‖^w
variable (V B:S.Tag)
variable (hc:S.Hierarchy)(hp:F.PointLimits C S)
variable (hq:Cells.CellHyp C F)(hC:C.Makes)(hm:W.Derivatives S)
variable (ℓ:∀i,Fin (n i)→ Cover){r:ℝ}(hL: ∀i,Injective (Fin.cons (α:=fun _=>Cover) 0 (ℓ i)))
    (hK':∀z∈K,∀ i,Locations C J r (ℓ i) (z i))(hr:0<r)
set_option maxHeartbeats 600000
include hc hp hC hq hm hK hsafe hK' hL hr hT hh hG
local notation "Ne₀"=> Note C.S

def outputCost (C:Family G)(S:Table C.book)(m J k D:ℕ)(A E:ℝ) := ‖LinearMap.toContinuousLinearMap (S.project D)‖*(lista C D m*(2*E))
def error (C:Family G)(m J k:ℕ)(A:ℝ):= A*((2:ℝ)*(Accent.stakes C J k / pitts C m))
lemma pack (D:ℕ) (w:ℝ)(hw:0<w): ∃ (A s β:ℝ)(j:ℕ→ℕ)(k:ℕ) (E:ℕ→ℝ), 1<s∧0<β∧Ne₀ E β∧0<A ∧0<s∧β<w∧ Tendsto j atTop atTop∧ Tendsto (fun m:ℕ=> C.S.scale (j m)/C.S.scale m) atTop (𝓝 s)∧ ∀ᶠ m in atTop,∀ r, (R') m≤ r→ r≤(Yb) m→ ∀ z∈K, ∀ y∈arena r, taper (C.S.a (j m)) y=Set.univ → ∃v:S.Field D,bonded q V B y ((R') m ^ ((B.1:ℝ)+V.1-D)) D z v (outputCost C S m J k D A (E m)) (error C m J k A):=by
    let k0:= (Stock.Tabs.mayOpen C.path.levels 1 hT.opens J).choose; let k:= max k0 (C.ref D)
    let qV:=S.representative V.1 V.2; let qB:=S.representative B.1 B.2
    let w':= max ((C.labels.level V.1).coeffSize qV) ((C.labels.level B.1).coeffSize qB) + 1
    let hh' := (w/2)
    obtain ⟨t,j,H⟩:= hh.fees' B.1 V.1 D J k hh' (half_pos hw) (Stock.Tabs.open_later _ _ hT.opens ((Stock.Tabs.mayOpen C.path.levels 1 hT.opens J).choose_spec) (le_max_left ..) zero_le_one) (le_max_right ..) w' (show 0<w' from by have hv:= Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ:Finset (C.labels.level V.1).Index)) => norm_nonneg (qV i)); dsimp only [w']; change (0:ℝ)≤ (C.labels.level V.1).coeffSize qV at hv; linarith only [le_max_left ((C.labels.level V.1).coeffSize qV) ((C.labels.level B.1).coeffSize qB),hv])
    obtain ⟨hw',ht,hβ,hβ',hγ,hj,hJ,E,he,hf⟩:=H
    let h := (B.fst:ℝ)+V.fst-D
    obtain ⟨A,hA,hQ⟩:=comparableGrid (J:=J) (t:=V.1) (d:=B.1) (m:=0) q ℓ hc hp hq hC hL hr
    have hV:V=(⟨V.1,S.project _ qV⟩:S.Tag):=(congr_arg (fun x:S.Field V.1=>Sigma.mk V.1 x) (S.rep _ V.2)).symm
    have hB:B=(⟨B.1,S.project _ qB⟩:S.Tag):=(congr_arg (fun x:S.Field B.1=>Sigma.mk B.1 x) (S.rep _ B.2)).symm
    let β:= -((B.1:ℝ)+V.1+8)*(1-t)
    refine ⟨A,t,β,j,k,E,ht,hβ,he.swapP (by ring),hA,by linarith,by change β≤w/2 at hγ; linarith,hj,hJ,?_⟩
    filter_upwards [within_reach K hK hsafe hT.notes, hf qB qV ((le_max_right ..).trans (le_add_of_nonneg_right zero_le_one)) ((le_max_left ..).trans (le_add_of_nonneg_right zero_le_one)) F] with m hf hw r hr₁ hr₂ z z0 y hy htp
    obtain ⟨c,hc,hN⟩:= read_grid (C:=C) htp
    rw [← hc] at hN hy ⊢; rw [hV,hB] -- leaves V.1 changed definally
    exact hQ qV qB m (j m) D h _ _ hw c (le_trans (by gcongr) hy.1.le) (le_trans hy.2.le (by gcongr)) z (hK' _ z0) (fun i=> slide_conf C.S _ (hf r hr₁ hr₂ z z0 _ hy i)) hN

omit hc hp hC hq hm hK hsafe hK' hL hr hT hh hG in
lemma errorNote (C:Family G)(J k:ℕ)(A:ℝ)(ha:0<A):Note C.S (fun m=>error C m J k A) (-(1/32)):=by
     have he(i):error C i J k A=A*(2* Accent.stakes C J k)/pitts C i:=by unfold error; ring
     rw [funext he]
     exact ((Note.notes C.S _ (mul_pos ha (mul_pos zero_lt_two (Real.exp_pos _)))).splits (Note.bell_exp C.S ((1:ℝ)/32))).swapP (by ring)

set_option linter.unusedVariables false
lemma signedNear (D:ℕ):predicate K q V B (silent q S D) (-(B.1:ℝ)-V.1+D+1/64) :=by
     obtain ⟨A,s,β,j,k,E,hs,hβ,hE,hA,hs',_,hj,hJ',H⟩:= pack hG K hK hsafe hT hh q V B hc hp hq hC hm ℓ hL hK' hr D 1 one_pos
     refine (Eq.mp ?_ (priced (h:=(B.1:ℝ)+V.1-D) K hK hsafe hT.notes q V B hc hp hq hC hm (errorNote C J k A hA) hs hj hJ' (silent q S D) hG ?_ (1/64) (by norm_num)))
     · apply congr_arg (predicate K q V B (silent q S D)); ring
     filter_upwards [H] with m hv r hr hr' z hz c hc hcancel y hy ht
     obtain ⟨v,h₀,hv⟩:= hv r hr hr' z hz y hy ht
     have he:(R') m≤r:=hr
     let w:=(R') m ^ ((B.1:ℝ)+V.1-D)
     change ‖w • (∑ i:ι, c i *twice _ _ _ _ _)‖ ≤ error _ _ _ _ _
     rw [Finset.smul_sum]; change ‖∑ i,↑w * (c i*twice _ V B _ _)‖ ≤ _

     have h':(∑ i:ι,↑w*(c i * twice (q i) V B y (z i)))=∑ i,c i*(↑w*twice (q i) V B y (z i)-once (q i) (⟨D,v⟩:S.Tag) (z i)):=by simp_rw [mul_sub,Finset.sum_sub_distrib,(show (∑ i,c i*once (q i) ⟨D,v⟩ (z i))=0 from hcancel v),sub_zero]; exact Finset.sum_congr rfl (fun i _=>by ring)
     rw [h']; let p:=error C m J k A; have hp:0 < p:= errorNote C J k A hA|>.pos m
     apply (norm_sum_le ..).trans ?_
     calc _ ≤ ∑ i:ι,‖c i‖*p:= Finset.sum_le_sum fun i _=> by rw [norm_mul];exact mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _)
          _ ≤ p:=by rw [← Finset.sum_mul];exact mul_le_of_le_one_left hp.le hc



-- normal estimate has any power loss, still signed separately by positive fixed exponent.
lemma unconditionedNear (ε:ℝ)(hε:0<ε):predicate K q V B (fun _ _=>True) (-(B.1:ℝ)-V.1-ε):=by
     obtain ⟨A,s,β,j,k,E,hs,hβ,hE,hA,hs',hβ',hj,hJ',H⟩:= pack hG K hK hsafe hT hh q V B hc hp hq hC hm ℓ hL hK' hr 0 ε hε
     let f (i:ι)(z:Points (n i)):= Work.A01.frontRead (S.classTokens∘q i) (Points.cons 0 z) 0
     have h0(i z v):once (q i) (⟨0,v⟩:S.Tag) z=f i z v:=(Work.A01.front_eval ..).symm
     obtain ⟨C₀,hC₀,hQ⟩:= normProd_bound K hK hsafe f fun i z hZ v=>by simpa only [← h0] using! once_tends (q i) _ hZ v hc
     let cost m:= E m + C₀*((‖LinearMap.toContinuousLinearMap (S.project 0)‖+1)*(lista C 0 m*(2*E m)))
     have hc0: Note C.S cost β := by
           have ht: Ne₀ (lista C 0) 0 :=by unfold lista; simp only [pow_zero,mul_one]; exact (futon C).scales C.path.levels.fits.mesh
           apply hE.extra ((((Note.notes C.S C₀ hC₀).mills ((Note.notes C.S (‖LinearMap.toContinuousLinearMap (S.project 0)‖+1) (by have h := norm_nonneg (LinearMap.toContinuousLinearMap (S.project 0)); positivity)).mills (ht.mills ((Note.notes C.S (2:ℝ) zero_lt_two).mills hE)))).swapP (by ring)))
     refine Eq.mp ?_ (priced (h:=(B.1:ℝ)+V.1) K hK hsafe hT.notes q V B hc hp hq hC hm hc0 hs hj hJ' (fun _ _=>True) hG ?_ (-ε) (by linarith only [hβ']))
     · apply congr_arg (predicate K q V B (fun _ _=>True)); ring
     filter_upwards [(errorNote C J k A hA).outweigh hE (by linarith),H] with m he h r hr hr' z hz c hc' _ y hy htp
     obtain ⟨v,hv,h1⟩:= h r hr hr' z hz y hy htp
     have hL := hc0.pos m
     have ha(i): ‖((R') m) ^ ((B.1:ℝ)+V.1) • twice (q i) V B y (z i)‖ ≤ cost m:= by
          set w := ((R') m)^((B.1:ℝ)+V.1)
          have he₁:= (h1 i).trans he
          simp only [Nat.cast_zero,sub_zero] at he₁
          calc _ ≤ ‖w • twice (q i) V B y (z i) - once (q i) ⟨0,v⟩ (z i)‖+‖once (q i) ⟨0,v⟩ (z i)‖ :=by rw [norm_sub_rev _ (once _ _ _), add_comm]; exact norm_le_insert (once _ _ _) _
               _ ≤ _:= add_le_add he₁ ((by
                    rw [h0]; refine (hQ z hz i v).trans (mul_le_mul_of_nonneg_left (hv.trans (mul_le_mul_of_nonneg_right (show ‖LinearMap.toContinuousLinearMap (S.project 0)‖ ≤ ‖LinearMap.toContinuousLinearMap (S.project 0)‖+1 from by linarith only) (by have he:=hc0.pos m; have he':=Finset.prod_nonneg (s:=Finset.range (m+1)) (f:=fun i=> (C.path.levels.params (i+1)).columns * (↑((C.S.block i).val))^0) (fun k _=>mul_nonneg (zero_le_one.trans (C.path.levels.params (k+1)).columns_ge) (by positivity : 0≤ ((C.S.block k).val :ℝ)^0)); exact mul_nonneg he' (mul_nonneg zero_le_two (hE.pos m).le)))) hC₀.le)))
               _ ≤ cost m := le_refl _
     unfold combo; rw [Finset.smul_sum]; apply (norm_sum_le ..).trans
     calc _ ≤ ∑ i:ι,‖c i‖*cost m:=Finset.sum_le_sum fun i _=>by change ‖↑((R') m^((B.1:ℝ)+V.1))*(c i*_)‖≤_; rw [mul_left_comm,norm_mul]; exact mul_le_mul_of_nonneg_left (ha i) (norm_nonneg _)
          _ ≤ cost m :=by rw [← Finset.sum_mul]; exact mul_le_of_le_one_left hL.le hc'
end YM.MultipleContact.Local
