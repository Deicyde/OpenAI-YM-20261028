import YM.RG08.Trill.Cues
/-! # Criterion offshell. Lift counts & prices to Foot earlier. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Trill
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Skiff Trickle
open Room Gallery Camera Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Lagoon
open scoped Classical ContDiff BigOperators Topology ENNReal ComplexConjugate Matrix.Norms.Frobenius
variable {G:Gauge}{d n p l e D k i:ℕ}{σ B Q:ℝ}
local notation "E"=>Ed G Cover
local notation "Y"=>Snap G d
variable (X:Labels.Frame G d)
variable {P:GrainS (Ed G Cover)}
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- `Q` measured by ambient ℓ∞ on primary transfer & triangular. target only same e, n etc
 earlier projections not needed. Lower common hP at σ.
 full individual weights and normalized φ. h=d. -/
lemma listen (Ho:Hol G)(D:ℕ)(σ:ℝ)(hs:0<σ):∃ C:ℝ,0≤C ∧ ∀ (l:ℕ){P:GrainS (Ed G Cover)},Calls l P→Permit D l P→∀ (e n:ℕ)(B Q:ℝ),0≤B→0≤Q→(∀ i<e,∀ k≤l+i,Sings (stance _) D hs (P i k) B)→∀ (t:ℕ)(_h:k+t≤d)(_hl:n≤d)(s:Cargo t),
 let M:=harrow (P e n) (pal s) n d
 (∀ c:Accent X,(X.grades c.ear)=(k,n)→weight c.test.play=t→|project X P e c| ≤ Q)→∀ i:X.Index, |tally X n k i M| ≤ C*B+C*Q:=by -- k implicit constant from ambient, price uniform k by bind
 obtain ⟨D',hD,H⟩:=pix_prize X D σ hs
 let r:=∑ v:Cue d,(beta v.play:ℝ); have hr:0≤r:=Finset.sum_nonneg (by intros;positivity)
 refine ⟨r*(d*D'+1),by positivity,fun l P hc hp e n B Q hB hQ hP t h hl s ha i=>?_⟩
 obtain ⟨σ',hs',F,hF,H'⟩:= (hp.price e n).2
 let v:Cue d:=⟨Trill.capture s,by rw [weight_capture];omega⟩
 rw [cello_pal,harrow_test _ _ (hp.price e n).1 H' hF,_root_.map_smul,smul_eq_mul,abs_mul,abs_of_nonneg (show 0≤(beta (Trill.capture s):ℝ) by positivity)]
 apply LE.le.trans (b:=r*(d*D'*B+Q)) _ (by nlinarith only [mul_nonneg hr hB,show 0≤r*d*D'*Q by positivity]);apply mul_le_mul (a:= (beta (Trill.capture s):ℝ)) (b:=r) (single_le_sum (f:=fun v:Cue d=>(beta v.play:ℝ)) (by intros;positivity) (mem_univ v)) ?_ (abs_nonneg _) hr
 by_cases hx:(X.grades i)=(k,n)
 · let c:Accent X:={ear:=i,test:=v,joint:=by rw [hx];dsimp only [v];rw [weight_capture];exact h}
   have hh:= ha c hx (weight_capture s); rw [project_split] at hh
   change |tally X n k i (harrow (P e n) (celloTest v.play) n d)| ≤ _
   rw [show tally X n k i (harrow (P e n) (celloTest v.play) n d)=pix X i v.play (P e n) from by unfold pix; rw [hx]]
   let M:=∑ j∈range n,if n-j≤e then pix X i v.play (P (e-(n-j)) j) else 0
   change |(∑ j∈range (X.grades i).2,if _≤_ then _ else _) + pix X i v.play (P e ((X.grades i).2))| ≤ Q at hh -- leave placeholders
   rw [hx] at hh
   have hv:|M|≤d*D'*B:=by
      apply (abs_sum_le_sum_abs _ _).trans
      apply (sum_le_sum (g:=fun _=>D'*B) (fun j hj=>?_)).trans
      · rw [sum_const,card_range,nsmul_eq_mul,←mul_assoc];gcongr
      have hJ:j<n:=mem_range.mp hj;split_ifs with hg
      · let y:=e-(n-j)
        by_cases hj:P y j=0
        · change |pix X i v.play (P y j)|≤_;rw [hj]
          have hz: harrow (0:Gras G j) (celloTest v.play) (X.grades i).2 d=0:=by unfold harrow;rw [show grants (0:Gras G j) _ _ d=(fun _=>0) from ?_,Tensor.coeff_zero];funext _;unfold grants; apply sum_eq_zero;intro j _; unfold sonic; simp [tote]
          unfold pix;rw [hz,map_zero,abs_zero];positivity
        apply H j (by omega) _ _ hB (hp.price y j).1 (hP y (by unfold y;omega) j (hp.lit y j hj)) i v
      simp;positivity
   nth_rw 1 [show pix X i v.play (P e n) = M+pix X i v.play (P e n)-M from by ring]; exact (abs_sub _ _).trans ((add_le_add hh hv).trans_eq (add_comm _ _))
 have hh:=tally_label X _ (harrow_tile hc hp Ho (e:=e) (n:=n) (celloTest v.play) (show k≤d by omega) hl) i
 rw [X.power_coefficient i (Ne.symm hx) (gradePart_mem (k,n) _)] at hh
 change |tally X n k i (harrow (P e n) (celloTest v.play) n d)| ≤ _
 rw [Complex.ofReal_eq_zero.mp hh,abs_zero]; positivity
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
/-- Explicit first-grade test, unsummed n before fees. q+n≤joint.
 Ward-normalized pickup. Shelf all. -/
lemma hymn (D n:ℕ)(σ:ℝ)(hs:0<σ)(Ho:Hol G):∃ C:ℝ,0≤C∧∀ {l:ℕ}{P:GrainS (Ed G Cover)}(e:ℕ),Calls l P→Permit D l P→∀ (q:ℕ)(s: Jetty.Cargo q)(t:Fin n→ℕ)(y:Fin n→Snap G d), q+(∑ i,t i)≤ d → n≤d→ (∀ i, throughSlot (y i) (t i))→∀(B Q:ℝ),0≤B→0≤Q→(∀ i<e,∀ k≤l+i,Sings (stance _) D hs (P i k) B)→(∀ c:Accent X, (X.grades c.ear).1+weight c.test.play≤q+(∑ j,t j)→(X.grades c.ear).2=n→weight c.test.play=q→ |project X P e c|≤Q)→
 |sonic (P e n) (pal s) (fun i=>pluck 1 (y i))| ≤ C*(B+Q)*∏ j,‖y j‖:=by
 choose C hC H using fun (b:Fin n→Fin (d-1))=>coinage X b
 choose c hc E' using fun (b:Fin n→Fin (d-1))=> listen (k:=rate b) X Ho D σ hs
 refine ⟨∑ b:Fin n→Fin (d-1),C b*c b,sum_nonneg fun b _=>mul_nonneg (hC b) (hc b),?_⟩
 intro l P e Hc Hp q s t y ht hn hb B Q hB hQ hx hk
 obtain ⟨σ',hs',D',hD,hd⟩:=(Hp.price e n).2
 rw [show (fun i=>pluck 1 (y i))=pluck 1 ∘ y from rfl,←grants_chord (Hp.price e n).1 hd hD (pal s) (Hp.fine (pal s) e n) y]
 let M:=harrow (P e n) (pal s) n d; have hs0:=harrow_sym (d:=d) (p:=n) (Hp.price e n).1 hd hD (pal s)
 let I:=Fin (d-1)
 have hg:y=fun i:Fin n=>∑ j:I,Pi.single j (y i j):=by funext i j;rw [Finset.sum_apply,sum_eq_single j];rw [Pi.single_eq_same]; intro k _ hk;rw [Pi.single_eq_of_ne hk.symm];simp
 change |M y| ≤ _
 nth_rw 1 [hg]; rw [M.map_sum (fun i j=>Pi.single j (y i j)),sum_mul,sum_mul] -- check
 apply (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _=>?_)
 have he:0≤C i*c i*(B+Q)*∏ j:Fin n,‖y j‖:=by have h₁:=hC i;have h₂:=hc i; have h₃:=prod_nonneg (s:=univ) (f:=fun j:Fin n=>‖y j‖) (fun _ _=>norm_nonneg _); positivity
 by_cases hy:∀ j:Fin n,(i j).val+2≤ t j
 · have h₁:rate i ≤ ∑ j:Fin n,t j:= Finset.sum_le_sum (fun j (_:j∈(Finset.univ:Finset (Fin n)))=>hy j)
   have h₂:rate i+q≤d:=by omega
   have hr:M∈Validity X n (rate i):=admission X M hs0 (harrow_tile Hc Hp Ho (pal s) (by omega:rate i≤d) hn) -- typo
   have hp:=H i M (c i*B+c i*Q) hr (by have :=hc i;positivity) (E' i l Hc Hp e n B Q hB hQ hx q h₂ hn s fun g hg h=>hk g (by rw [hg,h];dsimp;omega) (by rw [hg]) h)
   apply (Real.norm_eq_abs _).symm.trans_le
   change ‖per G i M (fun j=>y j (i j))‖ ≤ _
   exact ((per G i M).le_opNorm (fun j=>y j (i j))).trans ((mul_le_mul hp (Finset.prod_le_prod (fun _ _=>norm_nonneg _) fun j _=>(norm_le_pi_norm ..)) (Finset.prod_nonneg fun _ _=> norm_nonneg _) (hp.trans' (norm_nonneg (per G i M)))).trans_eq (by ring_nf; rfl))
 push Not at hy;obtain ⟨j,hj⟩:=hy
 have hh0:Pi.single (i j) (y j (i j))=(0:Snap G d):=by rw [hb j (i j) hj];ext k; simp
 rw [M.map_coord_zero j hh0,abs_zero];exact he
end YM.RG08.Trill
