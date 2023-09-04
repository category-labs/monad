import smtplib
import ssl
import sys
import argparse
import os.path
from email.message import EmailMessage
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from email.mime.application import MIMEApplication


def main():
    parser = argparse.ArgumentParser(
        description="Process Gmail password, and commit arguments."
    )

    parser.add_argument(
        "--gmail_user", type=str, help="Gmail App User (example: rene@monad.xyz)"
    )
    parser.add_argument("--gmail_password", type=str, help="Gmail App Password")
    parser.add_argument("--repo_url", type=str, help="URL of the repo")
    parser.add_argument("--commit", type=str, help="Git commit message")
    parser.add_argument(
        "--summary", type=str, help="Path to HTML file containing summary"
    )
    parser.add_argument(
        "--complete_results",
        type=str,
        help="Path to HTML file containing complete results",
    )
    parser.add_argument("--date", type=str, help="Date string")
    args = parser.parse_args()

    gmail_user = args.gmail_user
    gmail_password = args.gmail_password
    repo_url = args.repo_url
    commit = args.commit
    summary_filename = args.summary
    complete_results_filename = args.complete_results
    date = args.date

    port = 465
    smtp_server = "smtp.gmail.com"
    sender_email = gmail_user
    recipients = [
        # TODO: add more recipients
        "rene@monad.xyz",
    ]

    # TODO: display skipped tests

    msg = MIMEMultipart("mixed")
    # msg.attach(MIMEText(f"Running tests on branch {branch}, commit {repo_url}/commit/{commit}.", 'plain'))

    with open(summary_filename, "r") as summary:
        msg.attach(MIMEText(summary.read().strip(), "html"))
    with open(complete_results_filename, "r") as complete_results:
        attachment = MIMEApplication(
            complete_results.read(), Name=os.path.basename(complete_results_filename)
        )
        attachment[
            "Content-Disposition"
        ] = f'attachment; filename="{complete_results_filename}"'
        msg.attach(attachment)
    msg["Subject"] = f"Monad Ethereum Tests - {date}"
    msg["From"] = sender_email
    msg["To"] = ", ".join(recipients)

    context = ssl.create_default_context()
    with smtplib.SMTP_SSL(smtp_server, port, context=context) as server:
        server.login(sender_email, gmail_password)
        server.send_message(msg, from_addr=sender_email)


if __name__ == "__main__":
    main()
