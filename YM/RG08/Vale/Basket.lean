import YM.RG08.Vale.Steps
/-!
# Bulk single-mark primary. Slot diagonal; polynomial cancellations spent only on kernel costs
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Exterior Precision Push.AbsoluteSums Finset Function Filter Matrix Work.F08 Next.Free
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Place Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {p m c f L:Side}{R S:ℝ}{D d e j r n i k t:ℕ} {τ:ℕ}{F:Labels.Frame G d}{T:SectionData F}
variable {V U: EnvelopeU D R G r}
lemma bloom (i:WardBin.Board G d): sampled (WardBin.chip i)∈ rangeLt _ (generation (WardBin.key i)) := by
  let A: Fin 1 → Snap G d := fun _ => WardBin.chip i
  have hv (v:Fin 1): throughSlot (A v) (generation (WardBin.key i)) := by
    rintro m h; unfold A WardBin.chip; have hx : m ≠ i.1:= fun he=> Nat.lt_irrefl _ (he ▸ h); simp [hx]
  have hF (v:Fin 1): 0<(fun _: Fin 1=> generation (WardBin.key i)) v:= by change 0 < (i.1.val+2); omega
  have H:= Film.lane_polynomial (fun _ : Fin 1=> generation (WardBin.key i)) A hv hF
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,one_nsmul] at H
  suffices he : sampled (WardBin.chip i) = _ from he.symm ▸ H -- build
  ext1 x; ext1 j
  rw [Film.lane_mail]; simp [Film.sampleIn, iteratedFDeriv_one_apply, echoing, A,sampled]

lemma invest_more (H:Hol G)(x:Letter F)(hV:Toute V)(hU:Toute U)(hv:Polished V)(hp:Polished U): invest H (V+U) x=invest H V x+invest H U x := by
  let g:=coinsT D x.test; let i:=x.label; unfold invest graceT; rw [show plug g R ∘ (V+U) = _ from (funext fun i=>map_add (plug g R) (V i) (U i): plug g R ∘ (V+U)= (plug g R ∘ V)+(plug g R ∘ U)), ladle_add _ (dapple hV _) (dapple hU _) (polished_fun hv _) (polished_fun hp _),map_add]; rfl
lemma invest_sm (H:Hol G)(v:Letter F)(c:ℝ)(h:Toute V)(he:Polished V): invest H (c•V) v=c*invest H V v := by
  unfold invest graceT; rw [show plug (coinsT D v.test) R ∘ (c• V) = c • (plug (coinsT D v.test) R∘V) from funext fun _=>by simp,ladle_scale _ (dapple h _) (polished_fun he _) c, map_smul]; simp only [Pi.smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
lemma invest_sum {I:Type}{V:I→ EnvelopeU D R G r} (H:Hol G)(v:Letter F)(s:Finset I)(h:∀ i∈s,Toute (V i))(hp:∀ i∈s,Polished (V i)): invest H (∑ i∈s,V i) v=∑ i∈s,invest H (V i) v := by
  induction s using Finset.induction_on with
  | empty=>simp
  | insert i s hi ih=>
    have hu j (hj:j∈s):=hp j (mem_insert_of_mem hj); have hv j (hj:j∈s):=h j (mem_insert_of_mem hj)
    rw [sum_insert hi,sum_insert hi,invest_more H v (h _ (mem_insert_self ..)) (tot_sums hv) (hp _ (mem_insert_self ..)) (polished_sum hu),ih hv hu]
lemma tile_agrees (H:Hol G)(v:Letter F)(ht: Polished V) (hu: Toute U) (hv:Toute V)(hp:Polished U)(hr:slot v=r)(x:ℝ)(he:
    ∀ A:Fin r→WardBin.Board G d, WardBin.depth A=(F.grades v.label).1→
      pass U (fun i=> Place.sampled (WardBin.chip (A i))) (coinsT D v.test) = x * pass V (fun i=>Place.sampled (WardBin.chip (A i))) (coinsT D v.test)):
    invest H U v=x*invest H V v := by
  subst r; let a:=F.grades v.label; let φ:= coinsT D v.test; let L (V:EnvelopeU D R G (slot v)):= plug φ R ∘ V
  let P:=cook (dapple hu φ) (polished_fun hp _) H d (slot v); let Q:=cook (dapple hv φ) (polished_fun ht _) H d (slot v)
  have hP : gradePart a (basin P) = (x:ℂ) • gradePart a (basin Q) := by
    apply Subtype.ext; change (gradePart (a.1,slot v) (basin P)).val= (x:ℂ) • (gradePart (a.1,slot v) (basin Q)).val
    rw [basin_tile P (F.bound _) (slot_le ..),basin_tile Q (F.bound _) (slot_le ..),dif_pos rfl,dif_pos rfl]; unfold WardBin.tile; rw [Finset.smul_sum]; refine sum_congr rfl fun b hb=>?_ ; let g:=WardBin.chip ∘ b
    have hz : P.val g=x*Q.val g := by
      change amount (L U) d _ g=x*amount (L V) d _ g; rw [rank_launch _ (dapple hu φ).toTidy (polished_fun hp _),rank_launch _ (dapple hv φ).toTidy (polished_fun ht _)]
      have hW : wallet (L U) (fun i=>deckP (sampled (g i)))=x*wallet (L V) (fun i=>deckP (sampled (g i))) := he b (mem_filter.mp hb).2
      rw [hW]; ring
    rw [shade_all,shade_all,hz,mul_left_comm _ x,Complex.ofReal_mul,map_mul]; rw [Algebra.smul_def,show algebraMap ℂ (Labels.Pol G)=MvPolynomial.C from rfl]; unfold g; ring
  have hj : F.coords (basin P) v.label=(x:ℂ) * F.coords (basin Q) v.label := by rw [Film.costs_only,hP,map_smul]; exact congr_arg ((x:ℂ)*·) ((Film.costs_only F _ _).symm)
  have hx:graceT H U φ v.label=(x:ℂ)*graceT H V φ v.label:= by unfold graceT ladle; rw [dif_pos ⟨dapple hu φ,polished_fun hp _⟩,dif_pos ⟨dapple hv φ,polished_fun ht _⟩]; exact hj
  exact (congr_arg Complex.re hx).trans (by simp [invest,φ])

lemma transferred (H:Hol G)(h:1/2≤R)(K:Flight j t) (hp:0<S)(ht:4≤t)(hj:d≤ j)(p:Site K.L)(hx:Polished V)(he:Toute V)(hy:Abates V k)(v:Letter F)(hv:fee v≤k)(hf:slot v=r):
    invest H (halo p V (painted G (Carrier.linesOf K S))) v=height K.L (fee v)*invest H V v := by
  refine tile_agrees H v hx (paid_color he _ (Carrier.stored K S hp ht) p K.odd h) he (halo_all K.odd h (spray_whole K S hp ht) p hx) hf _ fun b hb=>?_
  have hg (i:Fin r):= bloom (b i); let A i:= generation (WardBin.key (b i))
  have hl:(∑ i,A i)+cashT v.test=fee v:= congr_arg (·+cashT v.test) hb
  rw [← hl]; refine halo_falls h K hp ht hy he.toTidy hx p _ _ A hg (fun i=>?_) (fun i=> by unfold A generation; omega) (hl.trans_le hv)
  apply le_trans (single_le_sum (fun i _=>Nat.zero_le (A i)) (mem_univ i)) _; exact ((le_trans (Nat.le_add_right ..) (hl.trans_le v.bill)).trans hj)
lemma payout (H:Hol G)(h:1/2≤R)(K:Flight j t)(hp:0<S)(ht:4≤t)(hj:d≤j)(hx:Polished V)(he:Toute V)(hy:Abates V k)(v:Letter F)(hv:fee v≤k)(hf:slot v=r)(n:ℕ):
    invest H (aboard n (painted G (Carrier.linesOf K S)) V) v=(K.L.val:ℝ)^n * height K.L (fee v) * invest H V v := by
  have hh p:= paid_color he _ (Carrier.stored K S hp ht) p K.odd h
  have he' p:= halo_all K.odd h (spray_whole K S hp ht) p hx
  unfold aboard; rw [invest_sm H v _ (tot_sums fun i _=>hh i) (polished_sum (fun i _=>he' i)), invest_sum H v _ (fun i _=> hh i) (fun i _=> he' i)]
  simp_rw [fun p => transferred H h K hp ht hj p hx he hy v hv hf]; rw [sum_const,card_univ,nsmul_eq_mul]; field_simp
lemma amount_empty (H:Hol G)(hx:Polished V)(he:Toute V)(hy:Abates V k) (v:Letter F)(hv:fee v < k)(hf:slot v=r): invest H V v=0 := by
  rw [tile_agrees H v (polished_zero _ _ _) he tot_zero hx hf 0,zero_mul]
  intro x hh; let p i:= generation (WardBin.key (x i))
  rw [hy _ p (fun i=>bloom (x i)) (v.test) ((congr_arg (·+cashT v.test) hh).trans_lt hv),zero_mul]
end YM.RG08.Vale
