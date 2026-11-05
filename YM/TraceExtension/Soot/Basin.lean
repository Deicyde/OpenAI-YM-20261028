import YM.TraceExtension.Soot.Bloom
/-! Generalize South/Swing to arbitrary masked kernels. on replicated joint/coarse at m stop. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open GridApprox.Joint GridApprox
variable {V:Type}[Fintype V][DecidableEq V]{B:Census V} {G:Gauge}(C:Family G)(N k m p d:ℕ)(H:C.Makes)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (o:∀ i:ℕ,V→Site (C.side i p))(s:V→ C.label d)(t:V→Motion)(w:ℝ){j:ℕ}
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
variable (L:Coefficient (C.labels.level d) (C.side k p))(X:Extra.Histories.Music (C.labels.level d) C.path N p)
local notation "ζ!"=> ζ d
variable (h:Scrim C W u ψ φ δ ζ r D){b:C.label d}{Z:∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)}{g:ℕ→ℝ} {Q:ℝ}
local notation "U₀"=> fun i:V=>stepUp (t i) (o N i) (initial Y! T N p (-b) 0)
local notation "τ"=> march (fun _:V=>w) φ m
variable {a:ℝ}
variable {G':Config G (C.side k p)→ℂ}{E:MergeProof.Response G (C.side k p)}{S e v':ℝ}
local notation "V₁"=> fun i:V=>stepUp (t i) (o k i) G'
def Melts (m:ℕ)(B:BudgetPoint) (a b c:ℝ):Prop:= 0<a ∧ a ≤ 1 ∧ 0 ≤ c ∧ 4 ≤ B.supportExponent ∧
    let r:=m*siteFactor B.B; let t:= b+r*Real.sqrt b + a+r*c; (((B.B+B.B+1)^4:ℕ):ℝ)*t ≤ 3∧Real.exp t-1 ≤ 1
local notation "Ω"=> march (fun _:V=>w/a) φ m
lemma reins (j:V) :∀ i:ℕ,march (fun _:V=>w) φ m i j = march (fun _:Unit=>w) φ m i ()
   | 0=> rfl
   | n+1 => by
      simp only[march]; split
      next h=>exact congr_arg (φ n*·) (reins j n)
      next=>rfl
local notation "s'!"=> C.path.levels.clock
local notation "v"=> birth B (R N) U₀
local notation "M!"=> (fun hm:k≤N=> couple (gust T N p N (birth (B) (R N) U₀) k hm) V₁)
local notation "f!"=> (fun i j=>liftF T Y! N p (t j) (fun x=>o x j) Z i)
local notation "λ!"=> (fun i j=>liftK T N p (t j) (fun x=>o x j) Z i)
include H h
lemma copious (hN:k<N)(hK:C.ref d ≤ m) (hk':m<k)(hw:0<w)(hX:FReach (φ:=φ) (ζ:=ζ) (D:=D) (ψ:=ψ) C N k m p d L X Q w Z g b hN.le)(hL: Sung Y! T N p C.params W ℓ X) (hp:∀ i:ℕ,C.ref d ≤ i→∀ hi:i<N, Carol Y! T N p i (D N p i hi) (X.tone (i+1)) (X.tone i) (ψ i)) (hZ':march (fun _:Unit=>w/a) φ m k () * bond C.path N p X k (-b) ≤ ζ d k)(hE':Buff (N:=N) G' E S L e) (hHa: march (fun _:Unit=>w) φ m k () * (‖alto T k d‖ * e) ≤ v') (hb: Occupancy (o k) j) (hM':Melts j (C.path.levels.budget k) a (C.path.levels.clock.forcedAllowance k) v') (hi:∀ b',profile (R N).activities ((X.tone N).plays b').forced=hook (R N).activities (R N).p.threshold (booster Y! (R N) 0 b'))
    (hO:Migrating T m p N o)(hd:Occupancy (o m) (r m))(hh:Drake B (T|>.levels.budget m).B (o m))(hE:Drake B (T|>.levels.budget k).B (o k))
    (hf':Integrable v (prior G _))(hZ:Integrable ((M!) hN.le) (prior G _)) :
      Served (R m) (f! m) (λ! m) (gust T N p k (M! hN.le) m hk'.le) (o m) (fun _=>w) (T|>.levels.budget m).supportExponent 1 ∧ Vault (fun _:V=>w) (f! m) (λ! m) 2 1:=by
    have hk := hk'.le
    have hF:Brine C.path m δ φ:=⟨fun i _=> h.costs.stay.water _ (Nat.zero_le i),fun i _=> h.costs.stay.mint _ (Nat.zero_le i),fun i _=> h.costs.stay.split _ (Nat.zero_le i),fun i _=> h.costs.stay.support _ (Nat.zero_le i)⟩
    have hG:Brine C.path k δ φ:=⟨fun i _=> h.costs.stay.water _ (Nat.zero_le i),fun i _=> h.costs.stay.mint _ (Nat.zero_le i),fun i _=> h.costs.stay.split _ (Nat.zero_le i),fun i _=> h.costs.stay.support _ (Nat.zero_le i)⟩
    let β:= -b; let x i:= march (fun _:Unit=>w) φ m i (); have hp' i (he:m ≤ i): 0 < x i:= march_pos _ _ _ _ _ (fun _=>hw) hF i he _
    obtain ⟨Y,hF',hX',hP,hV,hI⟩:= h.costs.heights d k N p (hK.trans hk) hN.le
    have hm :Migrating T m p k o:= ⟨fun i hi hp' => hO.mare i hi (hp'.trans hN)⟩
    have hy :Migrating T k p N o:= ⟨fun i hi hp' => hO.mare i (hk.trans hi) hp'⟩
    have hM:=desal C.path r m p N δ φ o (fun _=>w) (fun _=>hw) hF B hO hh h.costs.mom hd
    let Q:=gust T N p N v
    have ht:∀ i:ℕ,k ≤ i→∀ h:i<N, Q i h.le=(T|>.levels.clock.op i p).push (T|>.β N p (i+1)) (Q (i+1) h):=fun i _ h=>gust_step _ _ _ _ _ h
    have he:Q N le_rfl=v:=gust_base ..
    have ha' := hM'.1; let u₀(k):= march (fun _:Unit=>w/a) φ m k (); have hΩ(i)(hx:m ≤ i)(j:V):0 < Ω i j:= march_pos _ _ _ _ _ (fun _=>div_pos hw ha') hF i hx _
    have ha:=pollinate T C.params W φ ψ (ζ d) u δ r D p N k (Y!) X t (fun _ : V=>β) o (Ω k) H.wilson h.costs.cost h.costs.back hN.le (hΩ k hk) (H.sections d) (show Sung Y! T N p C.params W k X from ⟨hL.head,hN.le,fun i hi=>hL.earned _ (hK.trans (hk.trans hi)),fun i hi=>hL.step _ (hK.trans (hk.trans hi))⟩) hG hX' h.costs.mom (hM.occ k hk hN.le) hy hE h.costs.night hF' hP (by
      intro j; rw [reins]; exact hZ') hV hI (fun i hi=>hp i (hK.trans (hk.trans hi))) hi ht he (he.symm ▸ hf') k le_rfl hN.le
    rw [marines k φ (Ω k) (hΩ k hk),show topPitch C.path N k=_ from (if_neg (show ¬k=N from hN.ne):topPitch C.path N k=(T|>.levels.budget k).supportExponent)] at ha
    let f':= f!; let L':=λ!; let P:= R k; have hP := H.wilson.represents N p k hN.le; have hv: Melts j P.p a (s'!|>.forcedAllowance k) v':=by
       unfold P; rw[hP.vac];exact hM'
    let c:= X.tone k; have hhY := hL.earned k (hK.trans hk) hN.le
    obtain hS:= hhY.earns (-b)
    choose g₀ hg hf hΩ' using fun i:V=> bornK H (c.plays β) hN.le hS.1 hS.2 (t i) (o k i)
    choose g' U' hτ hU hx₀ hv' hK' using fun i:V=>boost H L G' E e hE' hN.le (t i) (o k i)
    let ψ' (i:V):= radiant (alto T k d) (t i) (o k i) (L.exponentialEntry 0 (Y!) P)
    -- type of hx₀ etc
    have hs:∀ i:V, τ k i ≤ a*Ω k i:=by
        intro u; apply le_of_eq; suffices h :∀ j:ℕ,τ j u=a* Ω j u from h _
        intro j; induction j with
        | zero=> change w = a*(w/a); field_simp
        | succ i IH=>
           simp only [march]; split
           · dsimp only; rw [IH]; ring
           change w=a*(w/a); field_simp
    let χ i:= soarK T N p X β (t i) (fun x=>o x i) k
    let φ' i:= soarF T Y! N p X β (t i) (fun x=>o x i) k; let ν W:= profile P.activities W
    have hR: χ=fun i=> ν (g₀ i):= funext fun i=> hΩ' i
    have h' :f' k=φ'+ψ' :=by
       funext j U; let f:= (o k j); let d':=(t j); unfold f' liftF radiant; rw [hX.exp]; unfold stepUp; simp_rw [Pi.smul_apply,Pi.add_apply]; rw [scalar_add]; change (_:ℂ)*_=(_ : ℂ)*_+_*_; rw [mul_add,add_comm]; rfl
    have hY : L' k=fun i=> ν (g₀ i) + ν (g' i):=by
       funext i; unfold L' liftK sunny; rw [hX.tank]; change _=profile P.activities (g₀ i)+ profile P.activities (g' i); rw [hx₀ i,← hΩ' i,floated_add H]; unfold sunny; rw[smul_add]; abel
    have hu:= cloth (u:=v') (r:=τ k) hv' (fun i=> by rw [reins]; exact hHa) (fun i=> (hM.pos _ hk hN.le _).le)
    have hR':Served P φ' (fun i=>ν (g₀ i)) (gust T N p N v k hN.le) (o k) (Ω k) P.p.supportExponent 1:=by
       rw[← hR,show P.p =_ from hP.vac]; exact ha
    have hl: Served (R k) (f' k) (L' k) ((M!) hN.le) (o k) (τ k) ((T|>.levels.budget k).supportExponent-4) 1:=by
       rw[h',hY,← hP.vac]
       apply cherish P (m:=j) (X:=ψ') (hM.pos k hk hN.le) (hΩ k hk) ha'.le hM'.2.1 hs hR' hb hP.good.labels hg hf _ (Real.sqrt_nonneg _) _ hv.2.2.1 hτ hU (fun i=>hK' i) (fun W=> (Tour.bright T H.wilson N p k hN.le W).ne') (sub_nonneg.mpr hv.2.2.2.1) hv.2.2.2.2
       · intro i; refine fellK H β hhY ((hM.pos k hk hN.le i).le) ?_ (hF'.coin k le_rfl); rw [reins]; exact hX.pay
       refine ⟨hu.yes,hu.tracks,fun i=>?_⟩; obtain ⟨f,hf,H'⟩:=hu.fee i; refine ⟨f,hf,le_trans (sum_le_sum fun j _=> ?_) H'⟩; gcongr;first| exact (hf ..).1|exact mul_nonneg (hM.pos k hk hN.le i|>.le) (hf j).1
       linarith
    obtain ⟨Y,hΛ,hγ,_⟩:= h.costs.heights d m N p hK (hk.trans hN.le)
    have H' i: (fun j=>τ j i)=x:=by
       funext j; induction j with
       | zero=>rfl
       | succ j IH=> unfold x march; split
                     next hj=> exact congr_arg (φ j * ·) IH
                     next=>rfl
    have hT(i:V) : ∃ g, Wakes T m k N p (fun j=>o j i) (fun j=>τ j i) (fun j=>f' j i) g D hN.le ∧ ∀ j:ℕ,m ≤ j→ j≤k→ profile (R j).activities (g j)=L' j i:= by
       rw [H']; exact chapter T C.params Y! (ζ d) ψ m k N p (t i) (fun j=>o j i) x D Z g H.wilson (H.sections d) hN.le hX.descent (fun j hj _=> hp' _ hj) (fun j hj _=> by rw [show x (j+1)=φ j*x j from by unfold x; rw [march,if_pos hj]]; exact mul_le_of_le_one_left (hp' _ hj|>.le) (hγ.level j hj)) hΛ (fun j hj hk'=> (congr_fun (hO.mare j hj (hk'.trans hN)) i).symm) (fun j hj hk'=> by obtain ⟨w,p,hx,hv⟩:=h.costs.night.days N p j (hk'.trans hN); exact hx.propagate)
    choose G' HG hQ using hT; let Y' m (i:V):= G' i m
    have hG' i (hi:m ≤ i) (hk':i≤k): L' i=tapes T p N Y' i:= funext fun t=> hQ t i hi hk'|>.symm
    rw [hG' k hk le_rfl] at hl; have H':=Accent.voyage T r δ u D N p hN.le o τ f' Y' H.wilson (desal C.path r m p k δ φ o (fun _=>w) (fun _=>hw) hF B hm hh h.costs.mom hd) h.costs.night HG hl hZ m le_rfl hk'
    rw [← hG' m le_rfl hk, marines m φ (fun _=>w) (fun _=>hw)] at H'
    have hE:=hX.descent.rates m le_rfl hk; rw [marines m φ _ (fun _=>hw)] at hE
    have hΖ(i:V)(U):= toasted C N m p d H Z (ζ d) hK (hk.trans hN.le) (t i) (o m i) (hX.descent.ticks _ le_rfl hk|>.2) hw.le hE (hΛ.coin m le_rfl) U
    exact ⟨H',⟨fun i U=> (hΖ i U).1,fun i U=> by rw [← Finset.mul_sum]; exact (hΖ i U).2⟩⟩
end YM.MergeProof.Accent
