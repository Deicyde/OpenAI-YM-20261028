import YM.RG08.Spin.Cork
/-! # Intertwiners on finite segment & primary spin. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Spin
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries Pivot Carrier Place Scores.Pages
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {G:Gauge}{E e r d τ D j t n k m l :ℕ}{R:ℝ}{F:Labels.Frame G d}{H:Hol G}{S:SectionData F}{s:Signed} -- c unbound
section
variable {I:Type}{u:I→Windows}{X:Chain}{V:ReadsU F D R}{T:ChartRatio G}{i:G.ColorIndex}
variable {p:KPrices X.kernel}{g:KGate p}{q:Lending G X.kernel}{V':Prism G X.kernel g q E}{h:1/2≤R}{hD:d+1≤D}{B:Signals p q E τ H S h hD}
lemma stepHon (he:Tights B V' i T u)(t : Wings u 1){U V:BoardU D R G}(hp:Marvel k U)(hv:Marvel k V)(hM:∀ m,Honor s U V m) (d m):
    Honor s (Needle.push (heights X i T t) k d U) (Needle.push (heights X i T t) k d V) m := by
    unfold Needle.push; refine rink _ ((he.fair _).pass h hp) ((he.fair _).pass h hv) ?_
    have ht:= X.packing i T he.hv he.hz t.cut; exact standing he.hz (he.hv t.i) h hp.hem hp.cap hv.cap hv.hem (X.metric t.N t.i) ⟨X.metric_whole ..,fun i=>X.metric_sym ..,fun a b vv=> ⟨_,X.canonical _ _ t.cut vv⟩⟩ ht.gets ht.halt ht.opens hp.wardrobe s hM m
lemma swapSig (s: Signed) (F:Labels.Frame G d) (p:PowerSeries ℝ)(b:Letter F)(D:ℕ): swapU p (fun i=>fluxO s F D i b)=fun i=>fluxO s F D i b:= by
    funext i; unfold swapU fluxO; rw [Matrix.of_apply]; exact PowerSeries.subst_C _
lemma risingTh (he:Tights B V' i T u) (t:Wings u 1) (b:Letter F)(hp:Boards V) :
   let U:= bureau V (fluxO s F D)
   uprise (heights X i T t) U b=bureau (uprise (heights X i T t) V) (fluxO s F D) b:= by
    intro U
    let F':= heights X i T t; let M:= U b
    rw [uprise, ← Taste.epoch_f _ (he.fair _) h ((stays hp (dilation_O s)).rank b) d (slot_le b)]
    rw [show bureau V (fluxO s F D) b=edgeBook V (fun i=> fluxO s F D i b) from rfl, study _ _ (he.fair _) h hp, swapSig]; rfl
lemma uput (he:Tights B V' i T u)(t:Wings u 1)(hV:Boards V) (hp:Spun s V) : Spun s (uprise (heights X i T t) V):= by
   intro b n; rw [← risingTh he t b hV]; exact stepHon he t ((stays hV (dilation_O s)).rank b) (hV.rank b) (hp b) d n
lemma tally_turn (H:Hol G) (hp : Boards V)(hv : Spun s V)(hd:d≤D) : atlas H V*fluxO s F D=fluxO s F D * atlas H V:= by
   rw [← tells H hp]; ext1 i b
   exact congr_fun (Atlas_h H F ((stays hp (dilation_O s)).rank b) (hp.rank b) ((stays hp (dilation_O s)).paid b) (hp.paid b) (hv b) hd) i |>.trans (Finset.sum_congr rfl (fun i _=>rfl)) -- matrix
-- extend in sector all morphisms without claiming trunc-invariance. keep τ
lemma extendO (V:ReadsU F D R) (x: Native (Letter F)) (hV:Boards V) (hs:Spun s V) (n : Side) : Honor s (edgeBook V (fluxO s F D *ᵥ x)) (edgeBook V x) n := by
    rw [← telephone]; let S:= bureau V (fluxO s F D); have ht : Boards S:= stays hV (dilation_O s)
    intro i φ e r v
    let T1:= plug φ R; let T2:= plug (twisting s φ) R
    have h (U:ReadsU F D R)(hp:Boards U) (z: Exam D) (i:Site n)(v:Link G n):
        rootSong (plug z R ∘ edgeBook U x e r) n i v=∑ b,∑ j∈ range (e+1),coeff j (x b)*rootSong (plug z R ∘ U b (e-j) r) n i v := by
      let H:= plug z R; let X b j:= H ∘ (coeff j (x b) • U b (e-j) r)
      rw [accounting,graft]; simp_rw [graft]
      have he (j b): Pens (X b j):= (hp.rank b|>.hem (e-j) r|>.pens|>.scale _).shaped _
      rw [root_sum _ _ (fun b=> ∑ j∈range (e+1), X b j) (fun b _=> Pens.additions (fun j _=> he j b)),Finset.sum_apply]
      apply Finset.sum_congr rfl; intro b _; rw [root_sum _ _ _ (fun j _=> he j b),Finset.sum_apply]; refine Finset.sum_congr rfl fun j _=> ?_
      rw [show X b j=coeff j (x b) •(H∘U b (e-j) r) from funext fun i=>map_smul H (coeff j (x b)) (U b (e-j) r i),root_scale _ (((hp.rank b).hem _ _).pens.shaped H)]; rfl
    change rootSong (plug φ R∘ edgeBook S x e r) n (s.act i) v=rootSong (plug (twisting s φ) R∘ edgeBook V x e r) n i _
    rw [h S ht, h V hV]; exact sum_congr rfl fun b _=> sum_congr rfl fun j _=> congr_arg (coeff j (x b)*·) (hs b n i φ (e-j) r v)
lemma repose_h (he:Tights B V' i T u)(t : Wings u 1)(hV:Spun s (Ye X i T B t.up)) :
   Spun s (Ye X i T B t.low) ∧ Commute (Te B i T t) (fluxO s F D) := by
   let A:=Ye X i T B t.up; let W:=Ye X i T B t.low; let Q:=Xe B i T t; let Z:= Te B i T t; let J:= fluxO s F D
   have hz:Spun s Q:= uput he t ((he.firs _).toBoards) hV
   have hp: Boards Q:= heart (he.fair t) h ((he.firs t.up).toBoards)
   have hh: Commute Z J:= tally_turn H hp hz (d.le_succ.trans hD)
   refine ⟨?_,hh⟩
   have hT := he.reads t
   have hu: W=bureau Q Z⁻¹:= by rw [show Q= bureau W Z from hT.2,←bureau_acts,Matrix.mul_nonsing_inv _ (recoupC hT.1), bureau_one]
   change Spun s W; rw [hu]; intro b n; rw [← bureau_acts, show Z⁻¹*fluxO s F D=J*Z⁻¹ from ?_]; exact extendO Q _ hp hz n -- q inference
   have hv := hT.1; have hp:=Matrix.mul_nonsing_inv Z (recoupC hv); have ht:=Matrix.nonsing_inv_mul Z (recoupC hv)
   calc Z⁻¹*J = Z⁻¹*J*(Z*Z⁻¹):=by rw [hp,mul_one]
        _ = J*Z⁻¹ := by rw [mul_assoc Z⁻¹,←mul_assoc J, ← hh.eq,← mul_assoc Z⁻¹ (Z*J) _, ← mul_assoc Z⁻¹ Z J,ht,one_mul]
local notation "Υ" => Ye X i T B
theorem rotated_graph (he:Tights B V' i T u)(t:Wings u 0)(s:Signed): Spun s (Υ t):= by
    generalize ht:t.N-t.i=k; induction k generalizing t with
    | zero=>
      have hx:t.N=t.i:= by have hh:=t.cut; omega
      unfold Ye; rw [hx,step_top]; exact outlines _ _ he.sound s _ _
    | succ k ih=>
      have h': t.i<t.N:= by omega
      let v: Wings u 1:= ⟨t.toLaunch,t.N,t.M,h',t.side⟩
      exact (repose_h he v (ih v.up (by change t.N-(t.i+1)=k; omega))).1
lemma turnedT (he:Tights B V' i T u)(t:Wings u 1)(s: Signed): Commute (Te B i T t) (fluxO s F D) := (repose_h he t (rotated_graph he t.up s)).2
end
end YM.RG08.Spin
