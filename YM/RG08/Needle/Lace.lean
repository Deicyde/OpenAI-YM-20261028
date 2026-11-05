import YM.RG08.Needle.Blot
/-!
# One-mark deterministic and strict split. OLD↔NEW to charge separately
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Needle
open RG Laurent Lattice Wilson Bloch Exterior Precision Push.AbsoluteSums Finset Function Filter Matrix Work.F08 Next.Free
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall Vale Reflect Staffer Loom PertExtension.Series.Radial PertExtension.Series.Tested
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{L c f p: Side}{v w R A B:ℝ}{D d e j r n i k t:ℕ}{τ:ℕ}
variable {X:Row (Park G L) (Loc G 1)} {V U: BoardU D R G}{H : Canticle (Park G L)}{M : Row (Fink G L) (Fink G L)}{Q: Cross L (Loc G 1) (Loc G 1)}{W : Repeated L}
lemma cream_plus (h:∀ i j,Tidy (U i j))(g:∀ i j,Tidy (V i j))(hR:1/2≤R)(hk:Odd L.val)(d:ℕ): cream d (U+V) L=cream d U L+cream d V L := by
  funext i r; rw [Pi.add_apply,Pi.add_apply]; unfold cream reelF; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _
  let A (U:BoardU D R G):= raysF j (U i r)
  rw [show raysF j ((U+V) i r)= A U+A V from sub_eq_iff_eq_add.mp ?_,smul_add]; rotate_left
  exact Eq.symm (by simpa using! rays_sub ((h i r).pens.plus (g i r).pens) (g i r).pens hR hk j)
lemma rays_weight (V:EnvelopeU D R G r)(h:Pens V)(p:Site L)(v:ℝ)(hR:1/2≤R)(hV:Odd L.val): raysF p (v•V)=v • raysF p V := by
  let W i:=Shade.readdress (V i) p; have ht:=rays_print h hR hV p
  have hv : (fun i=>readdress ((v • V) i) p)=v • W := funext fun i=>by simp only [readdress,hR,hV,true_and,↓reduceDIte,W,Pi.smul_apply]; rfl
  unfold raysF; rw [hv,shiftP,tub_scale ht v, spring_a (ht.pours _) v skylight_ok]; rfl
lemma cream_weight (h:∀ i j,Tidy (U i j))(hR:1/2≤R)(hk:Odd L.val)(t:ℝ)(d:ℕ): cream d (t • U) L=t • cream d U L := by
  funext i r; rw [Pi.smul_apply,Pi.smul_apply]; unfold cream; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro p _; unfold reelF; simp only [Pi.smul_apply,rays_weight _ (h _ _|>.pens) _ t hR hk,smul_comm t]
lemma cream_fem (m:ℕ)(U:BoardU D R G)(hR:1/2≤R)(hk:Odd L.val)(d:ℕ):cream d (fem m U) L=fem m (cream d U L):= by funext e r; unfold cream reelF fem; split_ifs <;> simp [*, rays_zeros hR hk]

lemma filop_plus (hp:Whole M)(h:Whole Q)(hu:Fits τ U)(hV:Fits τ V)(he: Odd L.val)(hf:∀ i j,Tidy (U i j))(hg : ∀ i j,Tidy (V i j)) (hP:Decked H)(hx:∀ i j,Tunable (H i j))(hR:1/2≤R)(d:ℕ):
    filop M Q H none τ d (U+V)=filop M Q H none τ d U+ filop M Q H none τ d V:= by
  have ⟨hA,Hw⟩:= creamy d L hu (fun i j=>(hf i j).pens) hR he
  have ⟨hB,Hz⟩:= creamy d L hV (fun i j=>(hg i j).pens) hR he
  funext i j; simp only [filop,cream_plus hf hg hR he,Pi.add_apply]
  have he:=veiled_whole hp; rw [washed_plus he hx Hw Hz τ,Pi.add_apply, Pi.add_apply]; exact spring_plus ((washed_duty he hx hP Hw hA).2 ..).pens ((washed_duty he hx hP Hz hB).2 ..).pens (scan_whole h)
lemma filop_scale (hp:Whole M)(h:Whole Q)(hu:Fits τ U)(he:Odd L.val)(hf:∀ i j,Tidy (U i j))(hx:∀ i j,Tunable (H i j))(hP:Decked H)(hr:1/2≤R)(d:ℕ)(w:ℝ): filop M Q H none τ d (w•U)= w• filop M Q H none τ d U:= by
  obtain ⟨hA,Hw⟩:= creamy d L hu (fun i j=>(hf i j).pens) hr he; have hz:=veiled_whole hp
  funext i r; simp only [filop,cream_weight hf hr he w,Pi.smul_apply]; rw [washed_a hz hx Hw w τ,Pi.smul_apply,Pi.smul_apply]; exact spring_a ((washed_duty hz hx hP Hw hA).2 ..).pens _ (scan_whole h)
lemma filop_epoch (hp:Whole M)(hu:Fits τ U)(he:Odd L.val)(hf:∀ i j,Tidy (U i j))(hx:∀ i j,Tunable (H i j))(hP:Decked H)(hr:1/2≤R)(hg:τ ≤ i)(d:ℕ): filop M Q H none i d U= filop M Q H none τ d U:= by
  obtain ⟨hA,Hw⟩:= creamy d L hu (fun i j=>(hf i j).pens) hr he
  funext n r; unfold filop; rw [washed_epoch (veiled_whole hp) hx Hw hP hA hg]
lemma filop_fem (hp:Whole M)(h:Whole Q)(hu:Fits τ U)(he:Odd L.val)(hf:∀ i j,Tidy (U i j))(hx:∀ i j,Tunable (H i j))(hP:Decked H)(hr:1/2≤R)(hg:τ ≤ i+j)(d:ℕ) : filop M Q H none i d (fem j U) = fem j (filop M Q H none τ d U):= by
  obtain ⟨hA,Hw⟩:= creamy d L hu (fun i j=>(hf i j).pens) hr he
  funext n r; unfold filop; rw [cream_fem _ U hr he d,wash_fem (veiled_whole hp) hx Hw hP hA hg]; unfold fem; split; rfl; exact spring_zero (scan_whole h)

lemma arise (Q:Cross L (Loc G 1) (Loc G 1))(hp:Whole Q)(hz:Odd L.val)(hx:1/2≤R)(P: BoardU D R G)(τ:ℕ)(he:Fits τ P)(hT:∀ i j,Tidy (P i j))(i r d:ℕ):
    spring (cream d P L i r) (scan Q)=aboard d Q (P i r) := by
  have ht:= hT i r; have hh:= spring_tidy (show Pens (cream d P L i r) from ((creamy d L he (fun i j=>(hT i j).pens) hx hz).2 _ _).pens) (scan_whole hp) -- fix
  apply envelope_ext; intro φ; let E:=plug φ R; apply Tidy.uniquely (Tidy.map _ hh) (Tidy.map _ (sailing hz hx ht hp))
  intro m; funext x
  let g:Ratio m (m*L):=⟨L,rfl⟩; have hs:= scan_at g Q x
  rw [spring_echo E (show Pens (cream d P L i r) from ((creamy d L he (fun i j=>(hT i j).pens) hx hz).2 _ _).pens) (scan_whole hp), spring_tell _ (((creamy d L he (fun i j=>(hT i j).pens) hx hz).2 _ _).pens.shaped E) (scan_whole hp),cream_present g ((scan Q).acts m *ᵥ x) 0 d i r _ ht.pens hx hz, hs,lodge_f]
  let A p:= Vale.halo p (P i r) Q; let C:=((L.val:ℝ)^d / Fintype.card (Site L)); have he p:= (halo_tid (w:=p) hz hx ht hp).pens
  have h: rootSong (E∘aboard d Q (P i r)) m 0 x=C*∑ p,rootSong (E∘A p) m 0 x:= by
    let T b:= E∘A b; have hp p:= (he p).shaped E
    unfold aboard; rw [show E∘ (_ • ∑ p:Site L,A p) = (C • ∑ p,T p) from ?_,root_scale _ (Pens.additions fun b _=>hp b) _,root_sum _ _ T (fun b _=> hp b), Pi.smul_apply,Finset.sum_apply]; rfl
    rw [show C=(_ * _) from (div_eq_mul_inv ..), ← graft]; exact funext fun j=>by simp
  apply Eq.trans _ h.symm; rw [Finset.mul_sum]; apply sum_congr rfl; intro j _; exact congr_arg (C*·) (halo_pay g (0:Site m) j Q _ ht φ hp hz hx x).symm

def halfU (s:ℕ)(K:Row (Park G L) (Park G L))(H:Canticle (Park G L))(τ:ℕ)(P:BoardU D R G)(e r:ℕ) := ∑ i∈range (windows τ e),murmur none K H (cream s P L) (i+1) e r
lemma opening (hX:Whole M)(hQ:Whole Q)(hT:∀ i j,Tidy (U i j))(hp:Fits τ U)(ht:1/2≤R)(hZ: Odd L.val)(hh: ∀ i j,Tunable (H i j)) (hS:Decked H)(d e r:ℕ):
    filop M Q H none τ d U e r=aboard d Q (U e r)+spring (halfU d (veiled M) H τ U e r) (scan Q) := by
  have hx (i):= quiet_tidily (veiled_whole hX) hh ((creamy d L hp (fun k j=>(hT k j).pens) ht hZ).2) none (i+1) e r
  have hz:= (creamy d L hp (fun k j=>(hT k j).pens) ht hZ).2 e r
  have hp':washed τ none (veiled M) H (cream d U L) e r= cream d U L e r + halfU d (veiled M) H τ U e r := by
    unfold washed; rw [sum_range_succ',murmur]; exact add_comm ..
  rw [filop,hp',spring_plus hz.pens (show Pens (halfU d (veiled M) H τ U e r) from Tidy.additions (s:=range _) (fun i _=>hx i)|>.pens) (scan_whole hQ),arise Q hQ hZ ht U τ hp hT e r]
end YM.RG08.Needle
